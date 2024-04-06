// Section 140.1: $fopen and $fclose

integer MessagesFile, DiagnosticsFile, AllFiles;

initial
begin
  MessagesFile = $fopen("messages.txt");
  if (!MessagesFile)
  begin
    $display("Could not open \"messages.txt\"");
    $finish;
  end

  DiagnosticsFile = $fopen("diagnostics.txt");
  if (!DiagnosticsFile)
  begin
    $display("Could not open \"diagnostics.txt\"");
    $finish;
  end

  AllFiles = MessagesFile | DiagnosticsFile | 1;

  $fdisplay(AllFiles, "Starting simulation /*...*/");
  $fdisplay(MessagesFile, "Messages from %m");
  $fdisplay(DiagnosticsFile, "Diagnostics from %m");

  /*...*/

  $fclose(MessagesFile);
  $fclose(DiagnosticsFile);
end


