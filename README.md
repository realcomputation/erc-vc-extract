# ERC Program Verification

**erc-vc-extract** is an _OCaml_ program which extracts verification condition of an annotated **ERC** program written by _Sewon Park @ KAIST._

- LiCS 2019 submission version of **erc-vc-extract** can be downloaded here: [download link]
- Under development versions of **erc-vc-extract** can be accessed at its git repository: [git link]

_OCaml_ is required to compile **erc-vc-extract**. You can build using ***make*** command.

```terminal
./erc-vc-extract program.erc
```
on an annotated (pre/postcondition and loop in/variant) program, generates the three files:

1. _program\_prec.v_ _Coq_ file contains definition and some facts about _prec_ function used in _program.v_. The _prec_ function is the precision embedding: $z \mapsto 2^z$. 
1. _protrm\_log.txt_ is a text file states how the trivial quantifiers were reduced during translating set—valued semantic in **ERC** into a predicate in our assertion language, first order logic of the two—sorted structure.
1. _program.v_ is a _Coq_ file containing the extracted verification conditions which are required to be proved in order to verify the **ERC** program. The _Coq_ file uses _program_prec.v_ file; hence the file should be compiled first: `coqc program_prec.v`

`examples/trisection/` in the downloaded files contains _trisection.erc_ which is the annotated **ERC** program for Trisection algorithm. The three files generated from **erc-vc-extract** (_trisection.v_ , _trisection\_prec.v_, _trisection\_log.txt_ ) can be found in the directory. _trisection\_poved.v_ is a _Coq_ file where the theorems in _trisection.v_ are proved.

1. _trisection.erc_ : annotated erc program for Trisection algorithm
1. _trisection\_prec.v_ : _Coq_ file defining the precision embedding
1. _trisection.v_ : _Coq_ file generated from **erc-vc-extract**
1. _trisection\_proved.v_ : _Coq_ file with the statements in _trisection.v_ proved.


## Actual Syntax of Annotated ERC Program
  
_ERClang.pdf_ in the downloaded files (repository) contains formal definition of syntax / semantics / verification rules of **ERC** program which the implementatio of **erc-vc-extract** is based on. However, the actual syntax of **ERC** described there and that are actually recognized by **erc-vc-extract** are slightly different.

### Syntax of Annotated ERC Program
#### syntax of assertion language

- _ltype_ := R **|** Z
- _type_ := _ltype_ **|** R(_nat_) **|** Z(_nat_)
- _lterm_ := _string_  **|**  _int_  **|**  _int_.0  **|**  prec(_lterm_)  **|**  _lterm_ + _lterm_  **|**  _lterm_ * _lterm_  **|**  _lterm_ - _lterm_  **|**  _lterm_ / _lterm_  **|**  - _lterm_  **|**  / _lterm_  **|**  _string_(_lterm_, ..., _lterm_)  **|**  proj(_lterm, lterm_)  **|**  sub(_lterm, lterm, lterm_)  **|**  ( _lterm_ )
- _fol_ := True  **|**  False  **|**  _lterm_ = _lterm_  **|**  _lterm_ > _lterm_  **|**  ~ _fol_  **|**  _fol_ -> _fol_ **|**  _fol_ /\ _fol_  **|**  _fol_ \/ _fol_  **|**  forall _string_ : _ltype_, _fol_  **|**  exists _string_ : _ltype_, _fol_  **|**  _string_[_lterm_, ..., _lterm]_  **|**  _string_[_lterm_, ..., _lterm_]

#### syntax of annotated statements  

- _btype_ := Real  **|**  Integer
- _dtype_ := _btype_  **|**  Real(_nat_)  **|**  Integer(_nat_)
- _term_ := _string_  **|**  _int_  **|**  _int_.0  **|**  _term_ + _term_  **|**  _term_ - _term_  **|**  - _term_  **|**  _term_ * _term_  **|**  _term_ / _term_  **|**  / _term_  **|**  _term_ = _term_  **|**  _term_ >
_term_  **|**  _term_ < _term_  **|**  ! _term_  **|**  _term_ && _term_  **|**  _term_  ||  _term_  **|**  select(_term_, _term_)  **|**  iota(_term_)  **|**  max(_term_, _term_)  **|**  pif(_term_, _term_, _term_)  **|**  string(_term_)  **|**  test(_term_)  **|**  (_term_)  
- _statement_ := skip  **|**  newvar _string_ := _term_  **|**  _string_ := _term_  **|**  _string_[_term_] := _term_  **|**  if _term_ then _statement_ else _statement_. **|** @invariant _fol_ @variant _lterm_ while _term_ do _statement_. **|**  _statement_; _statement_  **|**  { _statement_ }
  
#### syntax for annotated program

- assumption_block := 
@load _string_ : _ltype_ * ... * _ltype_ -> _ltype_ when _fol_ with _fol_ | ... | when _fol_ with _fol_ 
**|** @load _string_ : _ltype_ * ... * _ltype_ => _ltype_ when _fol_ with _fol_ | ... | when _fol_ with _fol_
**|** @assume _fol_
**|** @assume @Coq _string_
**|** @definition _string_ : _ltype_ * ... * _type_ -> Prop := _fol_


- Annotated ERC program:
  
```
assumption_block

@precondition fol
@postcondition fol

Input (string : dtype, string : dtype, ..., string : dtype)
statement
Return term
```
  
#### loading single and multi functions:

The original ***ERC*** forces domain and codomain of single and multivalued function symbols. When one defines the function symbols in **erc-vc-extract**, they can decide whether the function symbol is meant to be single--valued or multivalued:

``` 
@load f : Z * Z * Z => Z 
      when P1 with Q1 
    | when P2 with Q2 
    | ... 
    | when Pn with Qn
```
loads the multivalued function symbol `f` to the context where $P_i \to Q_i$ are its specification. During translating the semantic of a function--call of `f`, the symbol will disappear (since we do not have power object in our language) and will be replaced with a predicated generated using the specification. 

On the other hand,

``` 
@load g : Z * Z * Z -> R 
      when P1 with Q1 
    | when P2 with Q2 
    | ... 
    | when Pn with Qn
```
loads the function symbol `f` to the context and the function symbol won't disappear when we translate its function--call semantic; `f(x)` will be a number that is expressible in our language whose properties are defined by the specifications $P_i\to Q_i$.

The `Pi` and `Qi` in specification may refer to the functions input values; for an example, consider $f : R \times R \to R$ and we want to say $x>y \to f(x,y) > 10$.  Then, $P := x > y$ and $Q := f(x,y) >10$. The function values are referred with `@n` where n is an index of the arguments (starting from $1$) and `_` will denote the function value in `Q`. Therefore, the function $f$ can be specified as:
```
@load f : R * R -> R
	  when @1 > @2 -> _ > 10.0
```

#### Coq tag in assumption

Using `@assume fol` adds the `fol` as an axiom to our assertion logic. It will be used to impose some facts about the assumed abstract functions; for an example, **trisection.erc** works on a function symbol `f` which is not an input but an assumed function. Hence, uniqueness of its root may be assumed using `@assume exists k : R, f(k) = 0.0`.

Sometimes users will want to assume some fact using Coq defined predicate directly, instead of describing it in our assertion language. For an example, even if continuity of `f` can be described in our assertion language, in order to use Coq’s rich libraries reasoning about continuous functions’ properties, assuming the function’s continuity via $\epsilon-\delta$ won’t really help. Hence, using `@Coq` tag in `@assume` (`@assume @Coq continuity f`), **erc-vc-extract** will simply dump the whole string into _Coq_. However, it requires to be careful that if there is `@Coq` tag, **erc-vc-extract** doesn’t do any syntax or type checking.

#### defining predicate
This is not really a necessary feature; however, it makes writing an annotated **ERC** program much easier.
```
@definition uniq : R * R -> Prop := @1<@2 /\ f(@1) <0.0 < f(@2) /\ exists! z:R, (@1<z<@2 /\ f(z) = 0.0)
```
is defining the predicate $uniq(a,b) := f \;\text{has a uniq root in }\; (a,b)$. See that $n$''th argument of the predicate is accessed by `@n`. Defining the predicate, it can be used in elsewhere so that it works as an abbreviation. Predicate call is expressed with `[ ]`;e.g., `True /\ uniq[x, y]`.

#### pre and postcondition

Pre and postcondition needs to refer to program's input values and its output value. Program's input values can be referred by using the input variable's name. Program's output value in postcondition can be referred with the symbol `_`. Consider a program `P` that returns `1` when `x>y` and `0` when `y>x`. Then the pre/postcondition will be written as:

```
@precondition x>y \/ y>x
@postcondition x>y -> _ = 1 /\ y>x -> _ = 0
Input (x : Real, y : Real)
...
```

#### variable scoping:

At the current stage of development, all the variable names (for both programming variable and logical variable) should be distinct, even for bounded ones. It was made this way to ease developing trivial quantifier reduction. The current development tries to reduce all trivial quantifiers, then convert it to be a prenex form. After converting to a prenex form, it converts once again to DNF formula. On the DNF formula **erc-vc-extract** checks trivially true / false clauses of arithmetics:
```
(x > 10) /\ (x = 10) ... => false
```
If the second step of reduction only increases the number of literals, **erc-vc-extract** rolls back. Of course, having global distinction in variable is not really necessary, once we have an internal engine takes care of variable distinction, hence the restriction will be removed in the future.
