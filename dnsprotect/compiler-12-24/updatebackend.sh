# copy helper files
src=./backends/*.dfy
dst_dir=./dafny/Source/DafnyCore/Backends/Lucid/
dst_main=$dst_dir/Dafny-compiler-lucid.dfy
ast_copy=$dst_dir/AST.dfy

# Copy src to dst
cp $src $dst_dir

# Remove the first line from each .dfy file in dst_dir if it matches exactly 'include "AST.dfy"'
for file in "$dst_dir"/*.dfy; do
  sed -i '' '1{/^include "AST\.dfy"$/d;}' "$file"
done
rm $ast_copy