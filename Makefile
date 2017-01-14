.PHONY: agda

agda:
	cd agda; agda -i . -i /usr/share/agda-stdlib PHOML/Meta.agda
	cd agda; agda -i . -i /usr/share/agda-stdlib PHOML/Corollaries.agda
