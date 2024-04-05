#ifndef TASK_H
#define TASK_H

#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <unistd.h>

#define NUM_THREADS 4

// Task structure
typedef struct task {
    void (*function)(void*);
    void *data;
    int id;
} task_t;

// Task queue structure
typedef struct task_queue {
    task_t **tasks;
    int capacity;
    int size;
    int front;
    int rear;
    pthread_mutex_t lock;
    pthread_cond_t cond;
} task_queue_t;

// Function declarations
void initialize_task_queue(task_queue_t *queue, int capacity);
void destroy_task_queue(task_queue_t *queue);
void enqueue(task_queue_t *queue, task_t* task);
task_t* dequeue(task_queue_t *queue);
void *worker(void *param);
void task_function(void *arg);

#endif