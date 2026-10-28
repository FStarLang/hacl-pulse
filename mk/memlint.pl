#!/usr/bin/perl
# Source rules for scratch memory; see lib/Hacl.Mem.fsti and mk/lint.mk.
#
#   1. Every local array is registered for wiping the moment it exists:
#      `let mut x = [| v; n |];` is followed directly by `Mem.track x;`.
#      From there Pulse itself refuses a function that does not wipe it.
#   2. No other way of getting memory: Pulse.Lib.Vec, Pulse.Lib.Box,
#      Array.alloc and with_local are for Hacl.Mem only.
#   3. No discarding resources with drop_ (which could discard the
#      obligation to wipe), except where a module is explicitly allowed to.
#   4. Mem.nowipe (release without wiping) only in the hot leaves listed
#      in %nowipe_ok, whose temporaries the C compiler keeps in registers.
#   5. No way around the abstract Hacl.Zeroable, which says which element
#      types Mem.wipe may zero: no `friend Hacl.Zeroable`, and an assumed
#      zeroable instance only in the vector modules in %zeroable_assume_ok.
use strict; use warnings;

my %drop_ok = map { $_ => 1 } qw(lib/Hacl.Mem.fst lib/Hacl.Impl.Table.fst);
my %nowipe_ok = map { $_ => 1 } qw(
  code/curve25519/Hacl.Curve25519.Field64.fst:mrow_add
  code/curve25519/Hacl.Curve25519.Field64.fst:fmul
  code/curve25519/Hacl.Curve25519.Field64.fst:fsqr
  code/p256/Hacl.P256.Field64.fst:fmul
  code/p256/Hacl.P256.Field64.fst:mred
  code/p256/Hacl.P256.Field64.fst:fmul1
  code/p256/Hacl.P256.Field.fst:fsqr
  code/p256/Hacl.P256.Field.fst:fsqr1
  code/p384/Hacl.P384.Field64.fst:step
  code/p384/Hacl.P384.Field64.fst:mont
  code/p384/Hacl.P384.Field64.fst:mred
  code/p384/Hacl.P384.Field64.fst:msqr
  code/p384/Hacl.P384.Scalar64.fst:step
  code/p384/Hacl.P384.Scalar64.fst:mont
  code/hash/Hacl.Hash.SHA3.fst:keccak_impl
);
my %zeroable_assume_ok = map { $_ => 1 }
  qw(lib/Hacl.Vec128.fst lib/Hacl.Vec256.fst lib/Hacl.Vec512.fst);
my $bad = 0;
sub fail { my ($f, $s, $pos, $msg) = @_;
  my $line = 1 + (substr($s, 0, $pos) =~ tr/\n//);
  print STDERR "$f:$line: $msg\n"; $bad++ }

for my $f (@ARGV) {
  local $/; open my $fh, '<', $f or die "$f: $!"; my $s = <$fh>; close $fh;
  (my $code = $s) =~ s{\(\*(?!\)).*?\*\)}{ my $c = $&; $c =~ s/[^\n]/ /g; $c }gse;
  my $is_mem = $f =~ m{(^|/)lib/Hacl\.Mem\.fsti?$};
  while ($code =~ /let\s+mut\s+([\w']+)\s*=\s*\[\|.*?\|\]\s*;/sg) {
    my ($n, $p, $e) = ($1, $-[0], $+[0]);
    fail($f, $s, $p, "local array '$n' is not followed by 'Mem.track $n;'")
      unless substr($code, $e) =~ /\A\s*Mem\.track\s+\Q$n\E\s*;/;
  }
  (my $rel0 = $f) =~ s{^.*?((?:lib|code|tests)/)}{$1};
  while ($code =~ /\bfriend\s+Hacl\.Zeroable\b/g) {
    fail($f, $s, $-[0], "'friend Hacl.Zeroable' would allow unsound zeroable instances");
  }
  while ($code =~ /\bassume\s+val\s+[\w']+\s*:[^=]*?\bzeroable\b/sg) {
    fail($f, $s, $-[0], "assumed zeroable instance; only the vector modules may assume one")
      unless $zeroable_assume_ok{$rel0};
  }
  next if $is_mem;
  while ($code =~ /\b(Pulse\.Lib\.Vec|Pulse\.Lib\.Box|with_local|(?:A|Array|Pulse\.Lib\.Array)\.alloc|(?:A|Array|Pulse\.Lib\.Array)\.free)\b/g) {
    fail($f, $s, $-[0], "'$1' allocates outside Hacl.Mem; use Mem.alloc or a tracked local array");
  }
  (my $rel = $f) =~ s{^.*?((?:lib|code|tests)/)}{$1};
  while ($code =~ /\bnowipe\b/g) {
    my $p = $-[0]; my ($fn) = substr($code, 0, $p) =~ /.*\bfn\s+(\w+)/s;
    fail($f, $s, $p, "'Mem.nowipe' is only allowed in the hot leaves listed in mk/memlint.pl")
      unless defined $fn && $nowipe_ok{"$rel:$fn"};
  }
  next if $drop_ok{$rel};
  while ($code =~ /\bdrop_\b/g) {
    fail($f, $s, $-[0], "'drop_' can discard a wipe obligation; not allowed here");
  }
}
exit($bad ? 1 : 0);
