.PHONY: html

html:
	agda --html "--html-dir=./html/" \
	  "--compile-dir=./_build" \
	  "src/Agda-Container-Plus.agda"