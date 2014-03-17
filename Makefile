OCAMLC = ocamlc -g

EXEC = formuleTester

SRC_DIR = src/

SRC_RAW =	test.ml		\
		test2.ml

SRC = $(addprefix $(SRC_DIR), $(SRC_RAW))

OBJ = $(SRC:.ml=.cmo)

INTERFACE = $(SRC:.ml=.cmi)

.SUFFIXES: .ml .cmo .cmi

.ml.cmo:
	$(OCAMLC) -c $<

.ml.cmi:
	$(OCAMLC) -c $<

all:	$(EXEC)

$(EXEC):	$(OBJ)
	$(OCAMLC) -o $(EXEC) $(SRC)

clean:
	rm $(OBJ) $(INTERFACE)

fclean: clean
	rm $(EXEC)

re:	fclean all