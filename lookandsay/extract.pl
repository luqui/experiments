#!/usr/bin/perl

print "elements = [\n";

while (<>) {
    if (my ($name) = /A NAME="(..?)"/) {
        my @elts;
        until (@elts = (<> =~ m{<A HREF="#(..?)">}g)) { }
        print qq{    "$name" --> [ } . join(',', map { qq{"$_"} } @elts) . qq{ ],\n};
    }
}

print "    ]\n";
print "    where (-->) = (,)";
