# Makefile for CoqApp

# Coq compiler
COQC = coqc
COQDOC = coqdoc

# Directories
SRC_DIR = src
THEORIES_DIR = theories
EXAMPLES_DIR = examples
DOCS_DIR = docs

# Source files
SRC_FILES = $(wildcard $(SRC_DIR)/*.v)
THEORY_FILES = $(wildcard $(THEORIES_DIR)/*.v)
EXAMPLE_FILES = $(wildcard $(EXAMPLES_DIR)/*.v)

# Object files
OBJ_FILES = $(SRC_FILES:.v=.vo) $(THEORY_FILES:.v=.vo) $(EXAMPLE_FILES:.v=.vo)

# Default target
all: $(OBJ_FILES)

# Compile .v files to .vo files
%.vo: %.v
	$(COQC) -Q $(SRC_DIR) CoqApp -Q $(THEORIES_DIR) CoqApp.Theories -Q $(EXAMPLES_DIR) CoqApp.Examples $<

# Generate documentation
documentation: $(SRC_FILES) $(THEORY_FILES) $(EXAMPLE_FILES)
	mkdir -p $(DOCS_DIR)
	$(COQDOC) --html --utf8 -d $(DOCS_DIR) \
		-Q $(SRC_DIR) CoqApp \
		-Q $(THEORIES_DIR) CoqApp.Theories \
		-Q $(EXAMPLES_DIR) CoqApp.Examples \
		$(SRC_FILES) $(THEORY_FILES) $(EXAMPLE_FILES)

# Test that all files compile
test: all
	@echo "All files compiled successfully!"

# Clean compiled files
clean:
	find . -name "*.vo" -delete
	find . -name "*.vok" -delete
	find . -name "*.vos" -delete
	find . -name ".*.aux" -delete
	rm -rf $(DOCS_DIR)

# Dependencies (basic order)
$(SRC_DIR)/Logic.vo: $(SRC_DIR)/Basics.vo
$(SRC_DIR)/Algorithms.vo: $(SRC_DIR)/Basics.vo $(SRC_DIR)/Logic.vo

.PHONY: all clean test documentation 