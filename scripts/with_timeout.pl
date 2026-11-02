#!/usr/bin/perl
# with_timeout.pl SECONDS CMD ARGS...: run CMD in its own process group; after SECONDS kill the whole
# group (SAW and any solver it started) and exit 142. Otherwise exit with CMD's status.
use strict; use warnings; use POSIX ();
my $secs = shift @ARGV;
my $pid = fork();
die "fork: $!" unless defined $pid;
if ($pid == 0) { setpgrp(0, 0); exec @ARGV or die "exec: $!"; }
local $SIG{ALRM} = sub { kill 'KILL', -$pid; waitpid($pid, 0); exit 142; };
alarm $secs;
waitpid($pid, 0);
alarm 0;
exit(POSIX::WIFEXITED($?) ? POSIX::WEXITSTATUS($?) : 1);
