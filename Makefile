OCAMLC = ocamlc -g

EXEC = formuleTester

SRC_DIR = src/

SRC_RAW =	structure.ml	\
		projet.ml

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