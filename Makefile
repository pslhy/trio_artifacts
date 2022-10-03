.PHONY: all clean generate-data clean-data regenerate-data

all:
	make -C burst

clean:
	make -C burst clean

clean-data:
	make -C burst clean-data

clean-outs:
	make -C burst clean-outs

generate-outs:
	make -C burst generate-outs

generate-data:
	make -C burst generate-data

generate-all: all generate-data generate-outs

regenerate-data:
	make -C burst regenerate-data

hyper-clean: clean-data clean-outs clean

kick-the-tires:
	make -C burst kick-the-tires
	echo "Tires kicked successfully!"
