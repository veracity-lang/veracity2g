

all: /tmp/autogen_tasks.c task.c task.h helper.h helper_workload.c
	cp /tmp/autogen_tasks.c ./tmp_autogen_tasks.c
	gcc -Wall task.c tmp_autogen_tasks.c helper_workload.c -o runtasks