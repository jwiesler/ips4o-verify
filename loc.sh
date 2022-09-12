for f in src/de/wiesler/*.java; do
    spec=$(cat "$f" | egrep "@" | egrep -v "@\s*$" | egrep -v "@ //" | wc -l)
	code=$(cat "$f" | egrep -v "(@|^\s+$)" | wc -l)
	base=$(basename $f)
	echo "$base,$code,$spec"
done
