#include <arpa/inet.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include "queue.h"
#include "lib.h"
#include "protocols.h"
#include <stdbool.h>

// Defines to not use magic numbers
#define IP_PROTOCOL_TYPE 0x0800
#define ARP_PROTOCOL_TYPE 0x806
#define ICMP_PROTOCOL 1
#define BROADCAST_MAC "ff:ff:ff:ff:ff:ff"
#define EMPTY_MAC "00:00:00:00:00:00"
#define TTL_DEFAULT 100
#define MAX_ROUTING_ENTRIES 100000
#define MAX_ARP_ENTRIES 50

// Structure to hold information about packets awaiting ARP resolution
typedef struct
{
    char *packet_data;
    size_t packet_length;
    int outgoing_interface;
} packet_info_t;

/**
 * Comparison function for qsort to sort routing table by mask length (descending)
 * Longer masks (more specific routes) will come first
 */
int compare_routes(const void *a, const void *b)
{
    const struct route_table_entry *route_a = (const struct route_table_entry *)a;
    const struct route_table_entry *route_b = (const struct route_table_entry *)b;

    return ntohl(route_b->mask) - ntohl(route_a->mask);
}

/**
 * Find best matching route for a destination IP using longest prefix match
 * Returns the route with the longest matching prefix or NULL if no match is found
 */
struct route_table_entry *find_matching_route(uint32_t destination_ip,
                                              struct route_table_entry *routing_table,
                                              int table_size)
{
    struct route_table_entry *best_route = NULL;
    uint32_t longest_mask = 0;

    uint32_t dest_ip_host = destination_ip;

    // Iterate through the routing table to find best match
    for (int i = 0; i < table_size; i++)
    {
        uint32_t prefix_host = ntohl(routing_table[i].prefix);
        uint32_t mask_host = ntohl(routing_table[i].mask);

        // Check if this route matches our destination
        if ((dest_ip_host & mask_host) == prefix_host)
        {
            // If this is the first match or it has a longer mask than our current best
            if (best_route == NULL || mask_host > longest_mask)
            {
                best_route = &routing_table[i];
                longest_mask = mask_host;
            }
        }
    }

    return best_route;
}

/**
 * Look up an IP address in the ARP cache to find its MAC address
 * Returns pointer to ARP entry if found, NULL otherwise
 */
struct arp_table_entry *lookup_mac_address(uint32_t target_ip,
                                           struct arp_table_entry *arp_cache,
                                           int cache_size)
{
    if (!arp_cache || cache_size <= 0)
        return NULL;

    // Search the ARP cache from newest to oldest entries
    int index = cache_size - 1;
    while (index >= 0)
    {
        if (arp_cache[index].ip == target_ip)
            return &arp_cache[index];
        index--;
    }

    return NULL;
}

/**
 * Utility function to swap two MAC addresses
 */
void swap_ethernet_addresses(uint8_t *addr1, uint8_t *addr2)
{
    uint8_t temp[6];
    memcpy(temp, addr1, 6);
    memcpy(addr1, addr2, 6);
    memcpy(addr2, temp, 6);
}

/**
 * Create and send an ICMP error message (like Destination Unreachable or TTL Exceeded)
 * Reuses the received packet buffer to construct the response
 */
void create_icmp_error(char *original_packet, int packet_length,
                       int interface, int error_type)
{
    struct ether_hdr *eth_hdr = (struct ether_hdr *)original_packet;
    struct ip_hdr *ip_hdr = (struct ip_hdr *)(original_packet + sizeof(struct ether_hdr));

    // Save a copy of the original IP header for the ICMP error message
    char *original_ip_backup = malloc(sizeof(struct ip_hdr));
    if (!original_ip_backup)
        return;
    memcpy(original_ip_backup, ip_hdr, sizeof(struct ip_hdr));

    char *response = original_packet;

    // Calculate offsets for different parts of the packet
    size_t ip_offset = sizeof(struct ether_hdr);
    size_t icmp_offset = ip_offset + sizeof(struct ip_hdr);
    size_t original_ip_offset = icmp_offset + 8;
    size_t data_offset = original_ip_offset + sizeof(struct ip_hdr);

    int total_size = sizeof(struct ether_hdr) + sizeof(struct ip_hdr) + 8 + sizeof(struct ip_hdr) + 8;

    // Swap Ethernet addresses and set our MAC as source
    uint8_t temp_mac[6];
    memcpy(temp_mac, eth_hdr->ethr_dhost, 6);
    memcpy(eth_hdr->ethr_dhost, eth_hdr->ethr_shost, 6);
    get_interface_mac(interface, eth_hdr->ethr_shost);

    // Create the ICMP header
    struct icmp_hdr icmp_hdr;
    memset(&icmp_hdr, 0, sizeof(icmp_hdr));
    icmp_hdr.mtype = error_type;
    icmp_hdr.mcode = 0;
    icmp_hdr.un_t.echo_t.id = 0;
    icmp_hdr.un_t.echo_t.seq = 0;
    icmp_hdr.check = 0;

    // Copy part of the original payload or zero it out if too small
    if (packet_length >= sizeof(struct ether_hdr) + sizeof(struct ip_hdr) + 8)
    {
        memcpy(response + data_offset,
               original_packet + sizeof(struct ether_hdr) + sizeof(struct ip_hdr),
               8);
    }
    else
    {
        memset(response + data_offset, 0, 8);
    }

    // Build the ICMP error message with the original IP header
    memcpy(response + original_ip_offset, original_ip_backup, sizeof(struct ip_hdr));
    memcpy(response + icmp_offset, &icmp_hdr, 8);

    // Set up the new IP header
    ip_hdr->ver = 4;
    ip_hdr->tos = 0;
    ip_hdr->tot_len = htons(sizeof(struct ip_hdr) + 8 + sizeof(struct ip_hdr) + 8);
    ip_hdr->id = htons(1);
    ip_hdr->frag = 0;
    ip_hdr->ttl = TTL_DEFAULT;
    ip_hdr->proto = ICMP_PROTOCOL;

    // Swap IP addresses and set our IP as source
    ip_hdr->dest_addr = ip_hdr->source_addr;
    ip_hdr->source_addr = inet_addr(get_interface_ip(interface));

    // Calculate checksums for both ICMP and IP headers
    struct icmp_hdr *icmp_ptr = (struct icmp_hdr *)(response + icmp_offset);
    icmp_ptr->check = 0;
    icmp_ptr->check = htons(checksum((uint16_t *)icmp_ptr, 8 + sizeof(struct ip_hdr) + 8));

    ip_hdr->checksum = 0;
    ip_hdr->checksum = htons(checksum((uint16_t *)ip_hdr, sizeof(struct ip_hdr)));

    // Send the ICMP error message
    send_to_link(total_size, response, interface);

    free(original_ip_backup);
}

/**
 * Handle ICMP echo request (ping) by creating and sending an echo reply
 */
void handle_icmp_echo_request(char *packet, size_t length, int interface)
{
    struct ether_hdr *eth = (struct ether_hdr *)packet;

    // Swap source and destination MAC addresses
    swap_ethernet_addresses(eth->ethr_dhost, eth->ethr_shost);

    struct ip_hdr *ip = (struct ip_hdr *)(packet + sizeof(struct ether_hdr));

    // Swap source and destination IP addresses
    uint32_t temp_ip = ip->dest_addr;
    ip->dest_addr = ip->source_addr;
    ip->source_addr = temp_ip;

    // Change ICMP type from request (8) to reply (0)
    struct icmp_hdr *icmp = (struct icmp_hdr *)(packet + sizeof(struct ether_hdr) + sizeof(struct ip_hdr));
    icmp->mtype = 0;

    // Recalculate checksums for both IP and ICMP headers
    ip->checksum = 0;
    ip->checksum = htons(checksum((uint16_t *)ip, sizeof(struct ip_hdr)));

    icmp->check = 0;
    icmp->check = htons(checksum((uint16_t *)icmp, length - sizeof(struct ether_hdr) - sizeof(struct ip_hdr)));

    // Send the echo reply
    send_to_link(length, packet, interface);
}

/**
 * Process an ARP reply by updating the ARP cache and forwarding any queued packets
 */
void process_arp_reply(char *packet,
                       queue *packet_queue,
                       struct arp_table_entry *arp_cache,
                       int *arp_cache_size)
{
    // Create new ARP cache entry from the received reply
    struct arp_table_entry new_entry;
    struct arp_hdr *arp = (struct arp_hdr *)(packet + sizeof(struct ether_hdr));

    new_entry.ip = arp->sprotoa;
    memcpy(new_entry.mac, arp->shwa, 6);
    arp_cache[(*arp_cache_size)++] = new_entry;

    // Process queued packets that were waiting for this MAC address
    while (!queue_empty(*packet_queue))
    {
        packet_info_t *queued = (packet_info_t *)queue_deq(*packet_queue);
        if (!queued)
            break;

        // Update the destination MAC and send the packet
        struct ether_hdr *eth = (struct ether_hdr *)queued->packet_data;
        memcpy(eth->ethr_dhost, new_entry.mac, 6);

        send_to_link(queued->packet_length, queued->packet_data, queued->outgoing_interface);

        // Free the queued packet resources
        free(queued->packet_data);
        free(queued);
        break; // Process one packet at a time to avoid delays
    }
}

/**
 * Generate and send an ARP request to resolve an unknown MAC address
 */
void generate_arp_request(struct route_table_entry *route, int out_interface)
{
    int packet_size = sizeof(struct ether_hdr) + sizeof(struct arp_hdr);
    char *request_packet = malloc(packet_size);
    if (!request_packet)
        return;

    // Set up Ethernet header with broadcast destination
    struct ether_hdr *eth = (struct ether_hdr *)request_packet;
    hwaddr_aton(BROADCAST_MAC, eth->ethr_dhost);
    get_interface_mac(route->interface, eth->ethr_shost);
    eth->ethr_type = htons(ARP_PROTOCOL_TYPE);

    // Set up ARP header fields
    struct arp_hdr *arp = (struct arp_hdr *)(request_packet + sizeof(struct ether_hdr));
    arp->proto_type = htons(IP_PROTOCOL_TYPE);
    arp->hw_len = 6;
    arp->opcode = htons(1);  // ARP Request
    arp->hw_type = htons(1); // Ethernet
    arp->proto_len = 4;      // IPv4

    // Set our IP and MAC as source
    arp->sprotoa = inet_addr(get_interface_ip(route->interface));
    get_interface_mac(route->interface, arp->shwa);

    // Set target IP (next hop) and empty MAC
    arp->tprotoa = route->next_hop;
    hwaddr_aton(EMPTY_MAC, arp->thwa);

    // Send the ARP request
    send_to_link(packet_size, request_packet, route->interface);

    free(request_packet);
}

/**
 * Update Ethernet header for ARP reply
 */
void update_eth_header_for_arp_reply(struct ether_hdr *eth, uint8_t *interface_mac)
{
    // Swap Ethernet addresses and set our MAC as source
    uint8_t temp_mac[6];
    memcpy(temp_mac, eth->ethr_dhost, 6);
    memcpy(eth->ethr_dhost, eth->ethr_shost, 6);
    memcpy(eth->ethr_shost, interface_mac, 6);
}

/**
 * Update ARP header fields for reply
 */
void update_arp_header_for_reply(struct arp_hdr *arp, uint8_t *interface_mac)
{
    // Change operation code to ARP reply
    arp->opcode = htons(2);

    // Swap IP addresses
    uint32_t temp_ip = arp->sprotoa;
    arp->sprotoa = arp->tprotoa;
    arp->tprotoa = temp_ip;

    // Swap hardware addresses
    uint8_t temp_hw[6];
    memcpy(temp_hw, arp->shwa, 6);

    // Set our MAC as sender, original sender as target
    memcpy(arp->shwa, interface_mac, 6);
    memcpy(arp->thwa, temp_hw, 6);
}

/**
 * Create and send ARP reply in response to an ARP request
 */
void create_arp_reply(char *packet, int packet_length, int interface)
{
    // Get our interface MAC address
    uint8_t interface_mac[6];
    get_interface_mac(interface, interface_mac);

    struct ether_hdr *eth = (struct ether_hdr *)packet;

    // Update both Ethernet and ARP headers
    update_eth_header_for_arp_reply(eth, interface_mac);
    struct arp_hdr *arp = (struct arp_hdr *)(packet + sizeof(struct ether_hdr));
    update_arp_header_for_reply(arp, interface_mac);

    // Send the reply
    send_to_link(packet_length, packet, interface);
}

/**
 * Check if route exists, send ICMP error if not
 * Returns true if packet should be dropped, false if processing should continue
 */
bool handle_no_route(struct route_table_entry *route, char *packet_buffer,
                     size_t packet_length, int interface)
{
    if (!route)
    {
        // No route found, send ICMP destination unreachable
        create_icmp_error(packet_buffer, packet_length, interface, 3);
        return true; // Skip further processing
    }
    return false; // Continue processing
}

/**
 * Check if TTL is valid, send ICMP error if not
 * Returns true if packet should be dropped, false if processing should continue
 */
bool handle_ttl_expiry(struct ip_hdr *ip, char *packet_buffer,
                       size_t packet_length, int interface)
{
    if (ip->ttl <= 1)
    {
        // TTL exceeded, send ICMP time exceeded
        create_icmp_error(packet_buffer, packet_length, interface, 11);
        return true; // Skip further processing
    }
    return false; // Continue processing
}


/**
 * Main router function
 */
int main(int argc, char *argv[])
{
    // Buffer for received packets
    char packet_buffer[MAX_PACKET_LEN];

    // Initialize router
    init(argv + 2, argc - 2);

    // Allocate memory for routing table and ARP cache
    struct route_table_entry *routing_table = malloc(sizeof(struct route_table_entry) * MAX_ROUTING_ENTRIES);
    struct arp_table_entry *arp_cache = malloc(sizeof(struct arp_table_entry) * MAX_ARP_ENTRIES);
    if (!routing_table || !arp_cache)
    {
        fprintf(stderr, "Memory allocation failed\n");
        return -1;
    }

    // Load routing table from file
    int routing_entries = read_rtable(argv[1], routing_table);
    int arp_entries = 0;

    // Sort routing table by prefix length (longest prefix match)
    qsort(routing_table, routing_entries, sizeof(struct route_table_entry), compare_routes);

    // Create queue for packets waiting for ARP resolution
    queue pending_packets = queue_create();

    // Main packet processing loop
    while (1)
    {
        int incoming_interface;
        size_t packet_length;

        // Receive packet from any interface
        incoming_interface = recv_from_any_link(packet_buffer, &packet_length);
        DIE(incoming_interface < 0, "recv_from_any_links");

        // Get Ethernet header
        struct ether_hdr *eth = (struct ether_hdr *)packet_buffer;

        // Handle ARP packets
        if (eth->ethr_type == htons(ARP_PROTOCOL_TYPE))
        {
            struct arp_hdr *arp = (struct arp_hdr *)(packet_buffer + sizeof(struct ether_hdr));

            // Process ARP request
            if (ntohs(arp->opcode) == 1)
            {
                // Check if request is for one of our interfaces
                char *interface_ip = get_interface_ip(incoming_interface);
                if (interface_ip && arp->tprotoa == inet_addr(interface_ip))
                {
                    create_arp_reply(packet_buffer, packet_length, incoming_interface);
                }
            }
            // Process ARP reply
            else if (ntohs(arp->opcode) == 2)
            {
                process_arp_reply(packet_buffer, &pending_packets, arp_cache, &arp_entries);
            }
            continue; // Skip to next packet
        }

        // Handle IP packets
        if (eth->ethr_type == htons(IP_PROTOCOL_TYPE))
        {
            struct ip_hdr *ip = (struct ip_hdr *)(packet_buffer + sizeof(struct ether_hdr));

            // Validate IP checksum
            uint16_t received_checksum = ntohs(ip->checksum);
            ip->checksum = 0;
            uint16_t calculated_checksum = checksum((uint16_t *)ip, sizeof(struct ip_hdr));
            if (calculated_checksum != received_checksum)
            {
                // Invalid checksum, drop packet
                continue;
            }

            // Check if packet is for the router itself (ICMP)
            if (ip->proto == ICMP_PROTOCOL)
            {
                char *interface_ip = get_interface_ip(incoming_interface);
                bool is_for_our_interface = (interface_ip && ip->dest_addr == inet_addr(interface_ip));

                if (is_for_our_interface)
                {
                    // Handle ICMP echo request (ping)
                    struct icmp_hdr *icmp = (struct icmp_hdr *)(packet_buffer +
                                                                sizeof(struct ether_hdr) + sizeof(struct ip_hdr));

                    bool is_echo_request = (icmp->mtype == 8);
                    if (is_echo_request)
                        handle_icmp_echo_request(packet_buffer, packet_length, incoming_interface);

                    continue; // Skip forwarding
                }
            }

            // Find best route for packet using longest prefix match
            struct route_table_entry *route = find_matching_route(ntohl(ip->dest_addr), routing_table, routing_entries);

            // Check if route exists, send ICMP error if not
            if (handle_no_route(route, packet_buffer, packet_length, incoming_interface))
            {
                continue;
            }

            // Check TTL, send ICMP error if expired
            if (handle_ttl_expiry(ip, packet_buffer, packet_length, incoming_interface))
            {
                continue;
            }

            // Decrement TTL and update IP checksum
            ip->ttl--;
            ip->checksum = 0;
            ip->checksum = htons(checksum((uint16_t *)ip, sizeof(struct ip_hdr)));

            // Set source MAC address to outgoing interface
            get_interface_mac(route->interface, eth->ethr_shost);

            // Find destination MAC in ARP cache
            struct arp_table_entry *dest_arp = lookup_mac_address(route->next_hop, arp_cache, arp_entries);
            if (dest_arp)
            {
                // MAC found, update destination and forward packet
                memcpy(eth->ethr_dhost, dest_arp->mac, 6);
                send_to_link(packet_length, packet_buffer, route->interface);
            }
            else
            {
                // MAC not found, queue packet and send ARP request
                packet_info_t *pending = malloc(sizeof(packet_info_t));
                if (!pending)
                    continue;

                pending->packet_data = malloc(packet_length);
                if (!pending->packet_data)
                {
                    free(pending);
                    continue;
                }

                // Save packet for later processing
                memcpy(pending->packet_data, packet_buffer, packet_length);
                pending->packet_length = packet_length;
                pending->outgoing_interface = route->interface;
                queue_enq(pending_packets, pending);

                // Send ARP request to resolve next hop
                generate_arp_request(route, route->interface);
            }
        }
    }

    // Cleanup (unreachable in this implementation)
    free(routing_table);
    free(arp_cache);
    return 0;
}