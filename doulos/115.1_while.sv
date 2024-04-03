// Section 115.1: While

reg [15:0] Word;
bit [ 5:0] CountOnes;

while (Word)
begin
  if (Word[0])
    CountOnes = CountOnes + 1;
  Word = Word >> 1;
end


