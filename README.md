# Short paper : Automated Certification of Logic Programs Groundness Analysis

## Requirements

- SWI-Prolog [^1]
- GNU Bash [^2]
- GNU Make [^3]
- Vampire [^4]
- E Theorem Prover [^5]

## Configuration

Update the path to LPTP root directory in file `./src/system.pl` 
by revising the argument passed to `io__lptp_home/1` predicate. 
For example :

```shell
% [...]
% git clone https://github.com/atp-lptp/lptp /Users/local/lptp
io__lptp_home('/Users/local/lptp'),
% [...]
```

Export the variable `LPTP_ROOT_DIR` with same path as value
by modifying `./bin/lptp` file. 
For example :

```shell
export LPTP_ROOT_DIR='/Users/local/lptp'
```

See also [doc/README.md](./doc/README.md).

## Execution

Build LPTP binary from previous configuration

```shell
make lptp-swi
```

Run the groundness properties certification benchmark

```shell
make run-benchmark 
```
Enter the commands above in the terminal from the root of LPTP
- to generate inter-argument relations by abstract interpretation,
- to derive groundness properties and
- to certify derivations with LPTP for the following programs.

```
examples/filex/elem.pl
examples/filex/ex30.pl
examples/filex/expmr.pl
examples/filex/extrait_peep.pl
examples/filex/lex.pl
examples/filex/loop.pl
examples/filex/mini.pl
examples/filex/mr.pl
examples/filex/pi.pl
examples/filex/pq.pl
examples/filex/test.pl
examples/filex/testneg.pl
examples/filex/tiny.pl
examples/filex/addmul.pl
examples/filex/apprev.pl
examples/filex/average1.pl
examples/filex/derivDLS.pl
examples/filex/fib.pl
examples/filex/for.pl
examples/filex/mc_pera.pl
examples/filex/member.pl
examples/filex/micgram.pl
examples/filex/split.pl
examples/filex/testapp3.pl
examples/filex/trans.pl
lib/graph/transitiveclosure.pl
lib/list/list.pl
lib/list/permutation.pl
lib/list/reverse.pl
lib/list/suffix.pl
lib/nat/ackermann.pl
lib/nat/int.pl
lib/nat/nat.pl
lib/sort/mergesort.pl
lib/sort/sort.pl
 ```

List certification results obtained with Vampire [^4] and E Theorem Prover [^5]

```shell
make results-for-each-program
```

## License

See [License](./COPYING)

## Copyright

Copyright (C) 2024-...  
Thierry Marianne -- thierry.marianne@univ-reunion.fr  
Fred Mesnard -- frederic.mesnard@univ-reunion.fr  
Etienne Payet -- etienne.payet@univ-reunion.fr

[^1]: https://www.swi-prolog.org/Download.html
[^2]: https://www.gnu.org/software/bash/
[^3]: https://www.gnu.org/software/make/#download
[^4]: https://vprover.github.io/
[^5]: https://wwwlehre.dhbw-stuttgart.de/~sschulz/E/E.html 
