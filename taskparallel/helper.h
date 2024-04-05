#ifndef HELPER_H
#define HELPER_H

/* GLOBAL VARIABLES */
typedef struct node {
    int id;
    int flag;
    int value;
    struct node* inner_list;
    struct node* next;
} node_t;
typedef struct list {
    node_t* head; 
} list_t;

#endif