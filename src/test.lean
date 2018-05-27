/-example : 1 + 2222 = 2223 :=
begin
  reflexivity
end

theorem foo : 1 + (2222222222222 : nat)  = 2222222222223 :=
begin
  reflexivity
end
-/

theorem bar : 100003 + 100003 = 200006 :=
rfl


