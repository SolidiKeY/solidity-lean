/* wait4 reports kernel maximum child RSS; bulk timing output stays off Git. */
#define _GNU_SOURCE
#include <sys/resource.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
int main(int argc,char **argv) {
 if(argc<3) return 2;
 struct timespec a,b; struct rusage u; int status;
 clock_gettime(CLOCK_MONOTONIC,&a);
 pid_t p=fork(); if(p<0) return 125;
 if(p==0) { execvp(argv[2],argv+2); perror("execvp"); _exit(127); }
 if(wait4(p,&status,0,&u)<0) return 125;
 clock_gettime(CLOCK_MONOTONIC,&b);
 FILE *f=fopen(argv[1],"w"); if(!f) return 125;
 fprintf(f,"{\"wall_seconds\":%.9f,\"maximum_child_rss_kib\":%ld}\n",b.tv_sec-a.tv_sec+(b.tv_nsec-a.tv_nsec)/1e9,u.ru_maxrss); fclose(f);
 return WIFEXITED(status)?WEXITSTATUS(status):128+WTERMSIG(status);
}
