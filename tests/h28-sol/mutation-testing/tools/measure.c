#define _GNU_SOURCE
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/resource.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

/* External measurement only: Lean's kernel does not trust this program. */
int main(int argc, char **argv) {
    if (argc < 2) return 125;
    struct timespec start, finish;
    if (clock_gettime(CLOCK_MONOTONIC, &start)) return 125;
    pid_t child = fork();
    if (child < 0) return 125;
    if (child == 0) {
        execv(argv[1], argv + 1);
        perror("execv");
        _exit(127);
    }
    int status;
    struct rusage usage;
    pid_t got;
    do { got = wait4(child, &status, 0, &usage); } while (got < 0 && errno == EINTR);
    if (got < 0 || clock_gettime(CLOCK_MONOTONIC, &finish)) return 125;
    int code = WIFEXITED(status) ? WEXITSTATUS(status) : 128 + WTERMSIG(status);
    double elapsed = (double)(finish.tv_sec - start.tv_sec) +
                     (double)(finish.tv_nsec - start.tv_nsec) / 1000000000.0;
    fprintf(stderr, "\nH28_MEASURE {\"exit\":%d,\"signal\":%d,\"maxrss_kib\":%ld,\"seconds\":%.9f}\n",
            code, WIFSIGNALED(status) ? WTERMSIG(status) : 0, usage.ru_maxrss, elapsed);
    return code;
}
