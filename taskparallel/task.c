
#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <unistd.h>

#include "task.h"

extern task_t* autogen_loadtask(int i);
extern int autogen_taskcount();
extern void autogen_initialize();

int main() {
    pthread_t threads[NUM_THREADS];
    task_queue_t queue;


    // Create worker threads
    for (int i = 0; i < NUM_THREADS; i++) {
        if (pthread_create(&threads[i], NULL, worker, (void*)&queue)) {
            fprintf(stderr, "Error creating thread\n");
            return 1;
        }
    }

    autogen_initialize();

    // Load the tasks from the autogen tasks
    int num_tasks = autogen_taskcount();


    // Initialize task queue
    initialize_task_queue(&queue, num_tasks);


    // Add tasks to the queue
    for (int i = 1; i <= num_tasks; i++) {
        task_t* t = autogen_loadtask(i);
        enqueue(&queue, t);
    }

    // Wait for threads to finish
    for (int i = 0; i < NUM_THREADS; i++) {
        pthread_join(threads[i], NULL);
    }

    // Clean up
    destroy_task_queue(&queue);

    return 0;
}

void initialize_task_queue(task_queue_t *queue, int capacity) {
    queue->tasks = (task_t **)malloc(sizeof(task_t*) * capacity);
    queue->capacity = capacity;
    queue->size = 0;
    queue->front = 0;
    queue->rear = -1;
    pthread_mutex_init(&queue->lock, NULL);
    pthread_cond_init(&queue->cond, NULL);
}

void destroy_task_queue(task_queue_t *queue) {
    free(queue->tasks);
    pthread_mutex_destroy(&queue->lock);
    pthread_cond_destroy(&queue->cond);
}

void enqueue(task_queue_t *queue, task_t* task) {
    pthread_mutex_lock(&queue->lock);
    if (queue->size < queue->capacity) {
        queue->rear = (queue->rear + 1) % queue->capacity;
        queue->tasks[queue->rear] = task;
        queue->size++;
        pthread_cond_signal(&queue->cond);
    }
    pthread_mutex_unlock(&queue->lock);
}

task_t* dequeue(task_queue_t *queue) {
    pthread_mutex_lock(&queue->lock);
    while (queue->size == 0) {
        pthread_cond_wait(&queue->cond, &queue->lock);
    }
    task_t* task = queue->tasks[queue->front];
    queue->front = (queue->front + 1) % queue->capacity;
    queue->size--;
    pthread_mutex_unlock(&queue->lock);
    return task;
}

void *worker(void *param) {
    task_queue_t *queue = (task_queue_t*)param;
    while (1) {
        task_t* task = dequeue(queue);
        task->function(task->data);
    }
    return NULL;
}
