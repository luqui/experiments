
%.html: %.lhs
	cat $< | hscolour --html -lit | pandoc --no-wrap -S -f markdown -t html | sed 's/Cyan/Black/g' > $@
