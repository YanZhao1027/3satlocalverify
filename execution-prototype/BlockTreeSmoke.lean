import BlockTree

#eval Prototype.BlockTree.count (Prototype.BlockTree.groups 16)
#eval Prototype.BlockTree.count (Prototype.BlockTree.groups 128)
#eval (Prototype.activeVars (Prototype.BlockTree.toCNF (Prototype.BlockTree.groups 16))).card
#eval (Prototype.BlockTree.toCNF (Prototype.BlockTree.groups 16)).card
#eval (Prototype.activeVars (Prototype.BlockTree.toCNF (Prototype.BlockTree.groups 128))).card
#eval (Prototype.BlockTree.toCNF (Prototype.BlockTree.groups 128)).card
