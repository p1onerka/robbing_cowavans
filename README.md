
## About the project

This project allows you to compile your source files into RISC-V assembly. It can also be used as syntax analyzer (parser) by excluding RISC-V code generation out of the code.


## Features

- Syntax analizer
- RISC-V code generation
- Register allocation via Linear Scan algorithm
- Simplification of constants in arithmetic expressions before code generation


## Installation and launch

Make sure you have OCaml and Dune installed
```bash
sudo apt install opam
opam init 
opam install dune
```

Clone the project (or you can download it from Releases)

```bash
git clone https://github.com/p1onerka/robbing_cowavans
```

Go to the project directory

```bash
cd robbing_cowavans
```

Build Dune and run project using path to your source code file

```bash
dune build 
dune exec ./bin/main.exe *your path to source file*
```
The generated assembly file will be located in "out" folder


## File structure

```
bin
├── main
│  │
│  ├── model
│  │  ├── algorithms
lib
├── CCHeap
├── codegen RISCV
│  ├── codegen
│  ├── life intervals
├── helper functions
│  ├── binders (for error treatment)
├── parser
│  ├── constants simplification
│  ├── error processing
│  ├── expression parser
│  ├── file reading
│  ├── statement parser
│  ├── types
out
├── your generated code located here
test
├──
```


## Example of usage
```
func main() {
    acc:=1; n:=7;
    while n > 1 do
        acc := acc*n;
        n := n-1;
    done
}
```
converts into:
```
_start:
call main5
li a0, 0
li a7, 93
ecall

main5:
addi sp, sp, -16
sd ra, 8(sp)
sd s0, 0(sp)
addi s0, sp, 16
li a0, 1
li a1, 7
.while_41_lbl:
li a2, 1
ble a1, a2, .done_41_lbl
mul a0, a0, a1
li a2, 1
sub a1, a1, a2
j .while_41_lbl
.done_41_lbl:
mv a0, zero
ld ra, -8(s0)
ld s0, -16(s0)
jr ra

main5_end:
mv a0, zero
ld ra, -8(s0)
ld s0, -16(s0)
jr ra
```




## Credits

[OCaml-containers](https://github.com/c-cube/ocaml-containers) for using CCHeap


## Developers and contacts

- [@p1onerka](https://github.com/p1onerka) (tg @p10nerka)
- [@Szczucki](https://github.com/Szczucki) (tg @szcz00)


## Feedback

If you have any feedback, please reach out to us at xeniia.ka@gmail.com or nshchutskiy@gmail.com


## License

The project is distributed under [MIT](https://choosealicense.com/licenses/mit/) license. Check [LICENSE](https://github.com/p1onerka/robbing_cowavans/blob/main/LICENSE) for more information.

