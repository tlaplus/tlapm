#!/usr/bin/perl

foreach $file (@ARGV) {
    open (my $f, "$file") || die "$file: $!" ;
    my @lines = <$f> ;
    close $f ;
    open ($f, '>', $file) || die "$file: $!" ;
    for (my $i = 0 ; $i <= $#lines ; $i ++) {
        $oldline = $lines[$i] ;
        chop ($oldline) ;
        $newline = $oldline ;
        $newline =~ s/ +$// ;
        if ($newline ne $oldline) {
            print "${file}:${i}\n" ;
            print "- ${oldline}-\n" ;
            print "+ ${newline}+\n" ;
        }
        print { $f } "$newline\n" ;
    }
    close $f ;
}
