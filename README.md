# Vers une automatisation de la certification des propriétés de clôture pour Prolog

## Pré-requis:

- SWI-Prolog [^1]
- GNU Bash [^2]
- GNU Make [^3]

## Configuration

Mettre à jour le chemin vers la racine de LPTP dans le fichier `./src/system.pl` 
en modifiant l'argument passé au prédicat `io__lptp_home/1`. Par exemple :

```
% [...]
% git clone https://github.com/atp-lptp/lptp /Users/local/lptp
io__lptp_home('/Users/local/lptp'),
% [...]
```

Voir également [doc/README.md](./doc/README.md) original du projet LPTP en anglais.

## Exécution

```
# Construire le binaire de LPTP à partir de la configuration précédente
make lptp-swi

# Lancer le benchmark
make run-benchmark 
```

Entrer les commandes ci-avant dans le terminal depuis la racine de LPTP afin
- d'obtenir des relations inter-arguments par interprétation abstraite,
- de dériver des propriétés de clôture et
- de certifier les dérivations avec LPTP les programmes suivants.

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
