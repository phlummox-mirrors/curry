-- A simple test ensuring that record update expressions work (see also
-- rec001.curry, rec002.curry, and rec003.curry for variants of this
-- example)

data Item = File{ name :: String }
     	  | Directory { name :: String, contents::[Item] }
	  | Link{ name, original :: String }

-- NB the local variable name does not hide the record label
rename :: Item -> String -> Item
rename item name = item{ name = name }

infix 4 :=
data Assoc a b = (:=){ key :: a, val :: b }

update x y = map (upd x y)
  where upd x y z = if x == key z then z{ val = y } else z

newtype Identity a = Id{ unId :: a }

constant i z = i{ unId = z }

main = print (constant (Id z) (update 2 'b' [1:='a',(:=){key=2},3:='c']))
  where z free
