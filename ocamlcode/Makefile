erc-vc-extract: lexer.cmo ast.cmo  context.cmo typing.cmo logic.cmo wpcalc.cmo initialcoq.cmo exporter.cmo parser.cmo main.cmo 
	ocamlc -o erc-vc-extract str.cma lexer.cmo ast.cmo context.cmo errors.cmo typing.cmo logic.cmo canonical.cmo reduction.cmo log.cmo initialcoq.cmo exporter.cmo wpcalc.cmo parser.cmo main.cmo 
errors.cmo: errors.ml ast.ml context.ml
	ocamlc -c errors.ml
wpcalc.cmo: wpcalc.ml logic.cmo typing.cmo reduction.cmo canonical.cmo exporter.cmo log.cmo
	ocamlc -c wpcalc.ml
exporter.cmo: exporter.ml initialcoq.cmo
	ocamlc -c exporter.ml
initialcoq.cmo: initialcoq.ml
	ocamlc -c initialcoq.ml
log.cmo: log.ml
	ocamlc -c log.ml
canonical.cmo: canonical.ml logic.cmo 
	ocamlc -c canonical.ml
reduction.cmo: reduction.ml logic.cmo canonical.cmo log.cmo
	ocamlc -c reduction.ml
logic.cmo: logic.ml ast.cmo errors.cmo
	ocamlc -c logic.ml
typing.cmo: typing.ml context.cmo errors.cmo
	ocamlc -c typing.ml
context.cmo: context.ml ast.cmo
	ocamlc -c context.ml
ast.cmo: ast.ml
	ocamlc -c ast.ml
lexer.ml: lexer.mll parser.cmo
	ocamllex lexer.mll
parser.mli: parser.mly
	ocamlyacc -v parser.mly
parser.ml: parser.mli
	ocamlc -c parser.mli
lexer.cmo: lexer.ml parser.ml
	ocamlc -c lexer.ml
parser.cmo: parser.ml ast.cmo wpcalc.cmo
	ocamlc -c parser.ml
main.cmo: main.ml parser.cmo lexer.cmo
	ocamlc -c main.ml

clean:
	rm erc-vc-extract parser.output *.cmo *.cmi lexer.ml parser.mli parser.ml 
