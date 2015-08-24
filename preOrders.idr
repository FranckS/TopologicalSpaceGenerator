module preOrders

import Data.Vect

data myData  : Type where
	Ca : myData
	Hi : myData
	Pa : myData
	Sa : myData
	So : myData

-- Just the decidable equality
myData_eq : myData -> myData -> Bool
myData_eq Ca Ca = True
myData_eq Hi Hi = True
myData_eq Pa Pa = True
myData_eq Sa Sa = True
myData_eq So So = True
myData_eq _ _ = False


-- Bool extended with 'unknown'
data BoolExt : Type where
	TrueBE : BoolExt
	FalseBE : BoolExt
	UnknownBE : BoolExt


BoolExt_eq : BoolExt -> BoolExt -> Bool
BoolExt_eq TrueBE TrueBE = True
BoolExt_eq FalseBE FalseBE = True
BoolExt_eq UnknownBE UnknownBE = True
BoolExt_eq _ _ = False


relation : Type
relation = myData -> myData -> BoolExt



CheckEnding : myData -> myData -> relation -> relation
CheckEnding start ending rel = aux_checkEnding Ca rel where
	aux_checkEnding : myData -> relation -> relation
	aux_checkEnding Ca r = -- Does (Ca,start) belongs to the relation ? If so, then (Ca,ending) should be added as well
		if BoolExt_eq (r Ca start) TrueBE then aux_checkEnding Hi (\u,v => if myData_eq u Ca && myData_eq v ending then TrueBE else r u v) else r	
	aux_checkEnding Hi r = -- Does (Hi,start) belongs to the relation ? If so, then (Hi,ending) should be added as well
		if BoolExt_eq (r Hi start) TrueBE then aux_checkEnding Pa (\u,v => if myData_eq u Hi && myData_eq v ending then TrueBE else r u v) else r
	aux_checkEnding Pa r = -- Does (Pa,start) belongs to the relation ? If so, then (Pa,ending) should be added as well
		if BoolExt_eq (r Pa start) TrueBE then aux_checkEnding Sa (\u,v => if myData_eq u Pa && myData_eq v ending then TrueBE else r u v) else r
	aux_checkEnding Sa r = -- Does (Sa,start) belongs to the relation ? If so, then (Sa,ending) should be added as well
		if BoolExt_eq (r Sa start) TrueBE then aux_checkEnding So (\u,v => if myData_eq u Sa && myData_eq v ending then TrueBE else r u v) else r
	aux_checkEnding So r = -- Does (So,start) belongs to the relation ? If so, then (So,ending) should be added as well
		if BoolExt_eq (r So start) TrueBE then (\u,v => if myData_eq u So && myData_eq v ending then TrueBE else r u v) else r



CheckStart : myData -> myData -> relation -> relation
CheckStart start ending rel = aux_checkStart Ca rel where
	aux_checkStart : myData -> relation -> relation
	aux_checkStart Ca r = -- Does (ending,Ca) belongs to the relation ? If so, then (start,Ca) should be added as well
		if BoolExt_eq (r ending Ca) TrueBE then aux_checkStart Hi (\u,v => if myData_eq u start && myData_eq v Ca then TrueBE else r u v) else r	
	aux_checkStart Hi r = -- Does (ending,Hi) belongs to the relation ? If so, then (start,Hi) should be added as well
		if BoolExt_eq (r ending Hi) TrueBE then aux_checkStart Pa (\u,v => if myData_eq u start && myData_eq v Hi then TrueBE else r u v) else r
	aux_checkStart Pa r = -- Does (Pa,start) belongs to the relation ? If so, then (Pa,ending) should be added as well
		if BoolExt_eq (r ending Pa) TrueBE then aux_checkStart Sa (\u,v => if myData_eq u start && myData_eq v Pa then TrueBE else r u v) else r
	aux_checkStart Sa r = -- Does (Sa,start) belongs to the relation ? If so, then (Sa,ending) should be added as well
		if BoolExt_eq (r ending Sa) TrueBE then aux_checkStart So (\u,v => if myData_eq u start && myData_eq v Sa then TrueBE else r u v) else r
	aux_checkStart So r = -- Does (So,start) belongs to the relation ? If so, then (So,ending) should be added as well
		if BoolExt_eq (r ending So) TrueBE then (\u,v => if myData_eq u start && myData_eq v So then TrueBE else r u v) else r



generateAllReflRelation : List relation
generateAllReflRelation = aux Ca Ca (\x,y => if myData_eq x y then TrueBE else UnknownBE) where
	aux : myData -> myData -> relation -> List relation

	-- first argument is Ca
	aux Ca Ca r = aux Ca Hi r

	aux Ca Hi r = let newR1 = (\x,y => if (myData_eq x Ca) && (myData_eq y Hi) then FalseBE else r x y) in
					let newR2 = (\x,y => if (myData_eq x Ca) && (myData_eq y Hi) then TrueBE else r x y) in
						let newR2_bis = CheckEnding Ca Hi newR2 in
						let newR2_bis2 = CheckStart Ca Hi newR2_bis in
							if (not (BoolExt_eq (r Ca Hi) TrueBE)) then (aux Ca Pa newR1 ++ aux Ca Pa newR2_bis2)
							else aux Ca Pa newR2_bis2

	aux Ca Pa r = let newR1 = (\x,y => if (myData_eq x Ca) && (myData_eq y Pa) then FalseBE else r x y) in
					let newR2 = (\x,y => if (myData_eq x Ca) && (myData_eq y Pa) then TrueBE else r x y) in
						let newR2_bis = CheckEnding Ca Pa newR2 in
						let newR2_bis2 = CheckStart Ca Pa newR2_bis in
							if (not (BoolExt_eq (r Ca Pa) TrueBE)) then (aux Ca Sa newR1 ++ aux Ca Sa newR2_bis2)
							else aux Ca Sa newR2_bis2

	aux Ca Sa r = let newR1 = (\x,y => if (myData_eq x Ca) && (myData_eq y Sa) then FalseBE else r x y) in
					let newR2 = (\x,y => if (myData_eq x Ca) && (myData_eq y Sa) then TrueBE else r x y) in
						let newR2_bis = CheckEnding Ca Sa newR2 in
						let newR2_bis2 = CheckStart Ca Sa newR2_bis in
							if (not (BoolExt_eq (r Ca Sa) TrueBE)) then (aux Ca So newR1 ++ aux Ca So newR2_bis2)
							else aux Ca So newR2_bis2

	aux Ca So r = let newR1 = (\x,y => if (myData_eq x Ca) && (myData_eq y So) then FalseBE else r x y) in
					let newR2 = (\x,y => if (myData_eq x Ca) && (myData_eq y So) then TrueBE else r x y) in
						let newR2_bis = CheckEnding Ca So newR2 in
						let newR2_bis2 = CheckStart Ca So newR2_bis in
							if (not (BoolExt_eq (r Ca So) TrueBE)) then (aux Hi Ca newR1 ++ aux Hi Ca newR2_bis2)
							else aux Hi Ca newR2_bis2

	-- first argument is Hi
	aux Hi Ca r = let newR1 = (\x,y => if (myData_eq x Hi) && (myData_eq y Ca) then FalseBE else r x y) in
					let newR2 = (\x,y => if (myData_eq x Hi) && (myData_eq y Ca) then TrueBE else r x y) in
						let newR2_bis = CheckEnding Hi Ca newR2 in
						let newR2_bis2 = CheckStart Hi Ca newR2_bis in
							if (not (BoolExt_eq (r Hi Ca) TrueBE)) then (aux Hi Hi newR1 ++ aux Hi Hi newR2_bis2)
							else aux Hi Hi newR2_bis2

	aux Hi Hi r = aux Hi Pa r -- Only TrueBE for (Hi,Hi)

	aux Hi Pa r = let newR1 = (\x,y => if (myData_eq x Hi) && (myData_eq y Pa) then FalseBE else r x y) in
					let newR2 = (\x,y => if (myData_eq x Hi) && (myData_eq y Pa) then TrueBE else r x y) in
						let newR2_bis = CheckEnding Hi Pa newR2 in
						let newR2_bis2 = CheckStart Hi Pa newR2_bis in
							if (not (BoolExt_eq (r Hi Pa) TrueBE)) then (aux Hi Sa newR1 ++ aux Hi Sa newR2_bis2)
							else aux Hi Sa newR2_bis2

	aux Hi Sa r = let newR1 = (\x,y => if (myData_eq x Hi) && (myData_eq y Sa) then FalseBE else r x y) in
					let newR2 = (\x,y => if (myData_eq x Hi) && (myData_eq y Sa) then TrueBE else r x y) in
						let newR2_bis = CheckEnding Hi Sa newR2 in
						let newR2_bis2 = CheckStart Hi Sa newR2_bis in
							if (not (BoolExt_eq (r Hi Sa) TrueBE)) then (aux Hi So newR1 ++ aux Hi So newR2_bis2)
							else aux Hi So newR2_bis2

	aux Hi So r = let newR1 = (\x,y => if (myData_eq x Hi) && (myData_eq y So) then FalseBE else r x y) in
					let newR2 = (\x,y => if (myData_eq x Hi) && (myData_eq y So) then TrueBE else r x y) in
						let newR2_bis = CheckEnding Hi So newR2 in
						let newR2_bis2 = CheckStart Hi So newR2_bis in
							if (not (BoolExt_eq (r Hi So) TrueBE)) then (aux Pa Ca newR1 ++ aux Pa Ca newR2_bis2)
							else aux Pa Ca newR2_bis2

	-- first argument is Pa
	aux Pa Ca r = let newR1 = (\x,y => if (myData_eq x Pa) && (myData_eq y Ca) then FalseBE else r x y) in
					let newR2 = (\x,y => if (myData_eq x Pa) && (myData_eq y Ca) then TrueBE else r x y) in
						let newR2_bis = CheckEnding Pa Ca newR2 in
						let newR2_bis2 = CheckStart Pa Ca newR2_bis in
						if (not (BoolExt_eq (r Pa Ca) TrueBE)) then (aux Pa Hi newR1 ++ aux Pa Hi newR2_bis2)
						else aux Pa Hi newR2_bis2

	aux Pa Hi r = let newR1 = (\x,y => if (myData_eq x Pa) && (myData_eq y Hi) then FalseBE else r x y) in
					let newR2 = (\x,y => if (myData_eq x Pa) && (myData_eq y Hi) then TrueBE else r x y) in
						let newR2_bis = CheckEnding Pa Hi newR2 in
						let newR2_bis2 = CheckStart Pa Hi newR2_bis in
						if (not (BoolExt_eq (r Pa Hi) TrueBE)) then (aux Pa Pa newR1 ++ aux Pa Pa newR2_bis2)
						else aux Pa Pa newR2_bis2

	aux Pa Pa r = aux Pa Sa r -- Only TrueBE for (Pa,Pa)

	aux Pa Sa r = let newR1 = (\x,y => if (myData_eq x Pa) && (myData_eq y Sa) then FalseBE else r x y) in
					let newR2 = (\x,y => if (myData_eq x Pa) && (myData_eq y Sa) then TrueBE else r x y) in
						let newR2_bis = CheckEnding Pa Sa newR2 in
						let newR2_bis2 = CheckStart Pa Sa newR2_bis in
						if (not (BoolExt_eq (r Pa Sa) TrueBE)) then (aux Pa So newR1 ++ aux Pa So newR2_bis2)
						else aux Pa So newR2_bis2

	aux Pa So r = let newR1 = (\x,y => if (myData_eq x Pa) && (myData_eq y So) then FalseBE else r x y) in
					let newR2 = (\x,y => if (myData_eq x Pa) && (myData_eq y So) then TrueBE else r x y) in
						let newR2_bis = CheckEnding Pa So newR2 in
						let newR2_bis2 = CheckStart Pa So newR2_bis in
						if (not (BoolExt_eq (r Pa So) TrueBE)) then (aux Sa Ca newR1 ++ aux Sa Ca newR2_bis2)
						else aux Sa Ca newR2_bis2


	-- first argument is Sa
	aux Sa Ca r = let newR1 = (\x,y => if (myData_eq x Sa) && (myData_eq y Ca) then FalseBE else r x y) in
					let newR2 = (\x,y => if (myData_eq x Sa) && (myData_eq y Ca) then TrueBE else r x y) in
						let newR2_bis = CheckEnding Sa Ca newR2 in
						let newR2_bis2 = CheckStart Sa Ca newR2_bis in
						if (not (BoolExt_eq (r Sa Ca) TrueBE)) then (aux Sa Hi newR1 ++ aux Sa Hi newR2_bis2)
						else aux Sa Hi newR2_bis2

	aux Sa Hi r = let newR1 = (\x,y => if (myData_eq x Sa) && (myData_eq y Hi) then FalseBE else r x y) in
					let newR2 = (\x,y => if (myData_eq x Sa) && (myData_eq y Hi) then TrueBE else r x y) in
						let newR2_bis = CheckEnding Sa Hi newR2 in
						let newR2_bis2 = CheckStart Sa Hi newR2_bis in
						if (not (BoolExt_eq (r Sa Hi) TrueBE)) then (aux Sa Pa newR1 ++ aux Sa Pa newR2_bis2)
						else aux Sa Pa newR2_bis2

	aux Sa Pa r = let newR1 = (\x,y => if (myData_eq x Sa) && (myData_eq y Pa) then FalseBE else r x y) in
					let newR2 = (\x,y => if (myData_eq x Sa) && (myData_eq y Pa) then TrueBE else r x y) in
						let newR2_bis = CheckEnding Sa Pa newR2 in
						let newR2_bis2 = CheckStart Sa Pa newR2_bis in
						if (not (BoolExt_eq (r Sa Pa) TrueBE)) then (aux Sa Sa newR1 ++ aux Sa Sa newR2_bis2)
						else aux Sa Sa newR2_bis2

	aux Sa Sa r = aux Sa So r -- Only TrueBE for (Sa,Sa)

	aux Sa So r = let newR1 = (\x,y => if (myData_eq x Sa) && (myData_eq y So) then FalseBE else r x y) in
					let newR2 = (\x,y => if (myData_eq x Sa) && (myData_eq y So) then TrueBE else r x y) in
						let newR2_bis = CheckEnding Sa So newR2 in
						let newR2_bis2 = CheckStart Sa So newR2_bis in
						if (not (BoolExt_eq (r Sa So) TrueBE)) then (aux So Ca newR1 ++ aux So Ca newR2_bis2)
						else aux So Ca newR2_bis2

	-- first argument is So
	aux So Ca r = let newR1 = (\x,y => if (myData_eq x So) && (myData_eq y Ca) then FalseBE else r x y) in
					let newR2 = (\x,y => if (myData_eq x So) && (myData_eq y Ca) then TrueBE else r x y) in
						let newR2_bis = CheckEnding So Ca newR2 in
						let newR2_bis2 = CheckStart So Ca newR2_bis in
						if (not (BoolExt_eq (r So Ca) TrueBE)) then (aux So Hi newR1 ++ aux So Hi newR2_bis2)
						else aux So Hi newR2_bis2

	aux So Hi r = let newR1 = (\x,y => if (myData_eq x So) && (myData_eq y Hi) then FalseBE else r x y) in
					let newR2 = (\x,y => if (myData_eq x So) && (myData_eq y Hi) then TrueBE else r x y) in
						let newR2_bis = CheckEnding So Hi newR2 in
						let newR2_bis2 = CheckStart So Hi newR2_bis in
						if (not (BoolExt_eq (r So Hi) TrueBE)) then (aux So Pa newR1 ++ aux So Pa newR2_bis2)
						else aux So Pa newR2_bis2

	aux So Pa r = let newR1 = (\x,y => if (myData_eq x So) && (myData_eq y Pa) then FalseBE else r x y) in
					let newR2 = (\x,y => if (myData_eq x So) && (myData_eq y Pa) then TrueBE else r x y) in
						let newR2_bis = CheckEnding So Pa newR2 in
						let newR2_bis2 = CheckStart So Pa newR2_bis in
						if (not (BoolExt_eq (r So Pa) TrueBE)) then (aux So Sa newR1 ++ aux So Sa newR2_bis2)
						else aux So Sa newR2_bis2

	aux So Sa r = let newR1 = (\x,y => if (myData_eq x So) && (myData_eq y Sa) then FalseBE else r x y) in
					let newR2 = (\x,y => if (myData_eq x So) && (myData_eq y Sa) then TrueBE else r x y) in
						let newR2_bis = CheckEnding So Sa newR2 in
						let newR2_bis2 = CheckStart So Sa newR2_bis in
						if (not (BoolExt_eq (r So Sa) TrueBE)) then (aux So So newR1 ++ aux So So newR2_bis2)
						else aux So So newR2_bis2

	aux So So r = r :: Nil -- Only TrueBE for (So,So)


