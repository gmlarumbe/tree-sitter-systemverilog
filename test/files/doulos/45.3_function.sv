// Section 45.3: Function

function automatic integer fibonacci (input integer n);
  if (n <= 2)
    fibonacci = 1;
  else
    fibonacci = fibonacci(n-1) + fibonacci(n-2);
endfunction


