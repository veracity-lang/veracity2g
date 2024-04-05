#include "helper.h"
#include <stdlib.h>
#include <stdio.h>

// Function prototypes
node_t* create_node(int id, int flag, int value);
void add_to_outer_list(list_t* list, node_t* new_node);
node_t* generate_inner_list(int length);
int rand_range(int min, int max);

void print_structure(list_t* myList) {
    // For demonstration, print the structure
    node_t* current = myList->head;
    while (current != NULL) {
        printf("Outer Node ID: %d, Flag: %d, Value: %d\n", current->id, current->flag, current->value);
        node_t* innerCurrent = current->inner_list;
        printf("  Inner nodes: "); 
        while (innerCurrent != NULL) {
            printf("<ID:%d,F:%d,Val:%d>, ", innerCurrent->id, innerCurrent->flag, innerCurrent->value);
            innerCurrent = innerCurrent->next;
        }
        printf("\n");
        current = current->next;
    }
}

node_t* create_node(int id, int flag, int value) {
    node_t* node = (node_t*)malloc(sizeof(node_t));
    node->id = id;
    node->flag = flag;
    node->value = value;
    node->inner_list = NULL;
    node->next = NULL;
    return node;
}

void add_to_outer_list(list_t* list, node_t* new_node) {
    if (list->head == NULL) {
        list->head = new_node;
    } else {
        node_t* current = list->head;
        while (current->next != NULL) {
            current = current->next;
        }
        current->next = new_node;
    }
}

node_t* generate_inner_list(int length) {
    node_t* head = NULL;
    node_t* current = NULL;
    for (int i = 0; i < length; i++) {
        node_t* new_node = create_node(i, rand() % 2, rand() % 101);
        if (head == NULL) {
            head = new_node;
            current = head;
        } else {
            current->next = new_node;
            current = current->next;
        }
    }
    return head;
}

int rand_range(int min, int max) {
    return min + rand() % (max - min + 1);
}
