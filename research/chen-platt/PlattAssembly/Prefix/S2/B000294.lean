import PlattAssemblyKernel
import PlattCertificates.Count131072.C019408
import PlattCertificates.Count131072.C019409
import PlattCertificates.Count131072.C019410
import PlattCertificates.Count131072.C019411
import PlattCertificates.Count131072.C019412
import PlattCertificates.Count131072.C019413
import PlattCertificates.Count131072.C019414
import PlattCertificates.Count131072.C019415
import PlattCertificates.Count131072.C019416
import PlattCertificates.Count131072.C019417
import PlattCertificates.Count131072.C019418
import PlattCertificates.Count131072.C019419
import PlattCertificates.Count131072.C019420
import PlattCertificates.Count131072.C019421
import PlattCertificates.Count131072.C019422
import PlattCertificates.Count131072.C019423
import PlattCertificates.Count131072.C019424
import PlattCertificates.Count131072.C019425
import PlattCertificates.Count131072.C019426
import PlattCertificates.Count131072.C019427
import PlattCertificates.Count131072.C019428
import PlattCertificates.Count131072.C019429
import PlattCertificates.Count131072.C019430
import PlattCertificates.Count131072.C019431
import PlattCertificates.Count131072.C019432
import PlattCertificates.Count131072.C019433
import PlattCertificates.Count131072.C019434
import PlattCertificates.Count131072.C019435
import PlattCertificates.Count131072.C019436
import PlattCertificates.Count131072.C019437
import PlattCertificates.Count131072.C019438
import PlattCertificates.Count131072.C019439
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000294
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts19408 : List PrefixCut := [⟨30,155884360,155884449⟩,
⟨108,562876200,562876522⟩,
⟨128,667715411,667715796⟩]
theorem checked19408 : checkPrefixCuts (2^48) 2547777537 9 Manual.Count131072.C019408.packed 128 cuts19408 = true := by
 decide +kernel
def pointBounds19408 : List (Nat × Nat × Nat) := [(2547808256,99631317672338,99631697811893),(2547888128,99631724664178,99632104803966)]
theorem point_links_checked19408 : (cuts19408.take 2).map (fun c => (2547777537-1+2*2^9*c.k,99631161787978+c.lower,99631541927444+c.upper)) = pointBounds19408 := by
 decide +kernel
def cuts19409 : List PrefixCut := [⟨58,300703784,300703964⟩,
⟨128,666024069,666024465⟩]
theorem checked19409 : checkPrefixCuts (2^48) 2547908609 9 Manual.Count131072.C019409.packed 128 cuts19409 = true := by
 decide +kernel
def pointBounds19409 : List (Nat × Nat × Nat) := [(2547968000,99632130207173,99632510347204)]
theorem point_links_checked19409 : (cuts19409.take 1).map (fun c => (2547908609-1+2*2^9*c.k,99631829503389+c.lower,99632209643240+c.upper)) = pointBounds19409 := by
 decide +kernel
def cuts19410 : List PrefixCut := [⟨8,41756549,41756572⟩,
⟨86,446390463,446390725⟩,
⟨128,666100344,666100740⟩]
theorem checked19410 : checkPrefixCuts (2^48) 2548039681 9 Manual.Count131072.C019410.packed 128 cuts19410 = true := by
 decide +kernel
def pointBounds19410 : List (Nat × Nat × Nat) := [(2548047872,99632537284007,99632917424277),(2548127744,99632941917921,99633322058430)]
theorem point_links_checked19410 : (cuts19410.take 2).map (fun c => (2548039681-1+2*2^9*c.k,99632495527458+c.lower,99632875667705+c.upper)) = pointBounds19410 := by
 decide +kernel
def cuts19411 : List PrefixCut := [⟨36,184911293,184911399⟩,
⟨114,595263625,595263973⟩,
⟨128,667391509,667391899⟩]
theorem checked19411 : checkPrefixCuts (2^48) 2548170753 9 Manual.Count131072.C019411.packed 128 cuts19411 = true := by
 decide +kernel
def pointBounds19411 : List (Nat × Nat × Nat) := [(2548207616,99633346539095,99633726679844),(2548287488,99633756891427,99634137032418)]
theorem point_links_checked19411 : (cuts19411.take 2).map (fun c => (2548170753-1+2*2^9*c.k,99633161627802+c.lower,99633541768445+c.upper)) = pointBounds19411 := by
 decide +kernel
def cuts19412 : List PrefixCut := [⟨64,324294249,324294447⟩,
⟨128,663380727,663381126⟩]
theorem checked19412 : checkPrefixCuts (2^48) 2548301825 9 Manual.Count131072.C019412.packed 128 cuts19412 = true := by
 decide +kernel
def pointBounds19412 : List (Nat × Nat × Nat) := [(2548367360,99634153313560,99634533454791)]
theorem point_links_checked19412 : (cuts19412.take 1).map (fun c => (2548301825-1+2*2^9*c.k,99633829019311+c.lower,99634209160344+c.upper)) = pointBounds19412 := by
 decide +kernel
def cuts19413 : List PrefixCut := [⟨14,74222311,74222354⟩,
⟨92,484094251,484094541⟩,
⟨128,672955731,672956135⟩]
theorem checked19413 : checkPrefixCuts (2^48) 2548432897 9 Manual.Count131072.C019413.packed 128 cuts19413 = true := by
 decide +kernel
def pointBounds19413 : List (Nat × Nat × Nat) := [(2548447232,99634566622349,99634946763824),(2548527104,99634976494289,99635356636011)]
theorem point_links_checked19413 : (cuts19413.take 2).map (fun c => (2548432897-1+2*2^9*c.k,99634492400038+c.lower,99634872541470+c.upper)) = pointBounds19413 := by
 decide +kernel
def cuts19414 : List PrefixCut := [⟨42,220666256,220666386⟩,
⟨120,626647112,626647488⟩,
⟨128,667730421,667730823⟩]
theorem checked19414 : checkPrefixCuts (2^48) 2548563969 9 Manual.Count131072.C019414.packed 128 cuts19414 = true := by
 decide +kernel
def pointBounds19414 : List (Nat × Nat × Nat) := [(2548606976,99635386022025,99635766163991),(2548686848,99635792002881,99636172145093)]
theorem point_links_checked19414 : (cuts19414.take 2).map (fun c => (2548563969-1+2*2^9*c.k,99635165355769+c.lower,99635545497605+c.upper)) = pointBounds19414 := by
 decide +kernel
def cuts19415 : List PrefixCut := [⟨70,373940623,373940842⟩,
⟨128,674764043,674764440⟩]
theorem checked19415 : checkPrefixCuts (2^48) 2548695041 9 Manual.Count131072.C019415.packed 128 cuts19415 = true := by
 decide +kernel
def pointBounds19415 : List (Nat × Nat × Nat) := [(2548766720,99636207026813,99636587169270)]
theorem point_links_checked19415 : (cuts19415.take 1).map (fun c => (2548695041-1+2*2^9*c.k,99635833086190+c.lower,99636213228428+c.upper)) = pointBounds19415 := by
 decide +kernel
def cuts19416 : List PrefixCut := [⟨20,104800633,104800697⟩,
⟨98,513062334,513062637⟩,
⟨128,671195428,671195824⟩]
theorem checked19416 : checkPrefixCuts (2^48) 2548826113 9 Manual.Count131072.C019416.packed 128 cuts19416 = true := by
 decide +kernel
def pointBounds19416 : List (Nat × Nat × Nat) := [(2548846592,99636612650866,99636992793565),(2548926464,99637020912567,99637401055505)]
theorem point_links_checked19416 : (cuts19416.take 2).map (fun c => (2548826113-1+2*2^9*c.k,99636507850233+c.lower,99636887992868+c.upper)) = pointBounds19416 := by
 decide +kernel
def cuts19417 : List PrefixCut := [⟨48,257293546,257293696⟩,
⟨126,666744318,666744710⟩,
⟨128,677896924,677897323⟩]
theorem checked19417 : checkPrefixCuts (2^48) 2548957185 9 Manual.Count131072.C019417.packed 128 cuts19417 = true := by
 decide +kernel
def pointBounds19417 : List (Nat × Nat × Nat) := [(2549006336,99637436339207,99637816482388),(2549086208,99637845789979,99638225933402)]
theorem point_links_checked19417 : (cuts19417.take 2).map (fun c => (2548957185-1+2*2^9*c.k,99637179045661+c.lower,99637559188692+c.upper)) = pointBounds19417 := by
 decide +kernel
def cuts19418 : List PrefixCut := [⟨76,396076896,396077132⟩,
⟨128,666599253,666599644⟩]
theorem checked19418 : checkPrefixCuts (2^48) 2549088257 9 Manual.Count131072.C019418.packed 128 cuts19418 = true := by
 decide +kernel
def pointBounds19418 : List (Nat × Nat × Nat) := [(2549166080,99638253019481,99638633163147)]
theorem point_links_checked19418 : (cuts19418.take 1).map (fun c => (2549088257-1+2*2^9*c.k,99637856942585+c.lower,99638237086015+c.upper)) = pointBounds19418 := by
 decide +kernel
def cuts19419 : List PrefixCut := [⟨26,134596544,134596625⟩,
⟨104,537273601,537273921⟩,
⟨128,665350314,665350708⟩]
theorem checked19419 : checkPrefixCuts (2^48) 2549219329 9 Manual.Count131072.C019419.packed 128 cuts19419 = true := by
 decide +kernel
def pointBounds19419 : List (Nat × Nat × Nat) := [(2549245952,99638658138382,99639038282284),(2549325824,99639060815439,99639440959580)]
theorem point_links_checked19419 : (cuts19419.take 2).map (fun c => (2549219329-1+2*2^9*c.k,99638523541838+c.lower,99638903685659+c.upper)) = pointBounds19419 := by
 decide +kernel
def cuts19420 : List PrefixCut := [⟨54,292915687,292915858⟩,
⟨128,678565205,678565602⟩]
theorem checked19420 : checkPrefixCuts (2^48) 2549350401 9 Manual.Count131072.C019420.packed 128 cuts19420 = true := by
 decide +kernel
def pointBounds19420 : List (Nat × Nat × Nat) := [(2549405696,99639481807839,99639861952225)]
theorem point_links_checked19420 : (cuts19420.take 1).map (fun c => (2549350401-1+2*2^9*c.k,99639188892152+c.lower,99639569036367+c.upper)) = pointBounds19420 := by
 decide +kernel
def cuts19421 : List PrefixCut := [⟨4,20204054,20204066⟩,
⟨82,437858061,437858319⟩,
⟨128,669919089,669919485⟩]
theorem checked19421 : checkPrefixCuts (2^48) 2549481473 9 Manual.Count131072.C019421.packed 128 cuts19421 = true := by
 decide +kernel
def pointBounds19421 : List (Nat × Nat × Nat) := [(2549485568,99639887661411,99640267806035),(2549565440,99640305315418,99640685460288)]
theorem point_links_checked19421 : (cuts19421.take 2).map (fun c => (2549481473-1+2*2^9*c.k,99639867457357+c.lower,99640247601969+c.upper)) = pointBounds19421 := by
 decide +kernel
def cuts19422 : List PrefixCut := [⟨32,171669492,171669593⟩,
⟨110,576601780,576602121⟩,
⟨128,675956207,675956602⟩]
theorem checked19422 : checkPrefixCuts (2^48) 2549612545 9 Manual.Count131072.C019422.packed 128 cuts19422 = true := by
 decide +kernel
def pointBounds19422 : List (Nat × Nat × Nat) := [(2549645312,99640709045938,99641089191047),(2549725184,99641113978226,99641494123575)]
theorem point_links_checked19422 : (cuts19422.take 2).map (fun c => (2549612545-1+2*2^9*c.k,99640537376446+c.lower,99640917521454+c.upper)) = pointBounds19422 := by
 decide +kernel
def cuts19423 : List PrefixCut := [⟨60,314396667,314396854⟩,
⟨128,665876044,665876440⟩]
theorem checked19423 : checkPrefixCuts (2^48) 2549743617 9 Manual.Count131072.C019423.packed 128 cuts19423 = true := by
 decide +kernel
def pointBounds19423 : List (Nat × Nat × Nat) := [(2549805056,99641527729320,99641907874910)]
theorem point_links_checked19423 : (cuts19423.take 1).map (fun c => (2549743617-1+2*2^9*c.k,99641213332653+c.lower,99641593478056+c.upper)) = pointBounds19423 := by
 decide +kernel
def cuts19424 : List PrefixCut := [⟨10,51550973,51551004⟩,
⟨88,456114166,456114437⟩,
⟨128,674120500,674120898⟩]
theorem checked19424 : checkPrefixCuts (2^48) 2549874689 9 Manual.Count131072.C019424.packed 128 cuts19424 = true := by
 decide +kernel
def pointBounds19424 : List (Nat × Nat × Nat) := [(2549884928,99641930759670,99642310905500),(2549964800,99642335322863,99642715468933)]
theorem point_links_checked19424 : (cuts19424.take 2).map (fun c => (2549874689-1+2*2^9*c.k,99641879208697+c.lower,99642259354496+c.upper)) = pointBounds19424 := by
 decide +kernel
def cuts19425 : List PrefixCut := [⟨38,198244686,198244802⟩,
⟨116,605983455,605983814⟩,
⟨128,671105679,671106075⟩]
theorem checked19425 : checkPrefixCuts (2^48) 2550005761 9 Manual.Count131072.C019425.packed 128 cuts19425 = true := by
 decide +kernel
def pointBounds19425 : List (Nat × Nat × Nat) := [(2550044672,99642751573883,99643131720196),(2550124544,99643159312652,99643539459208)]
theorem point_links_checked19425 : (cuts19425.take 2).map (fun c => (2550005761-1+2*2^9*c.k,99642553329197+c.lower,99642933475394+c.upper)) = pointBounds19425 := by
 decide +kernel
def cuts19426 : List PrefixCut := [⟨66,345363160,345363365⟩,
⟨128,672726756,672727155⟩]
theorem checked19426 : checkPrefixCuts (2^48) 2550136833 9 Manual.Count131072.C019426.packed 128 cuts19426 = true := by
 decide +kernel
def pointBounds19426 : List (Nat × Nat × Nat) := [(2550204416,99643569798036,99643949944834)]
theorem point_links_checked19426 : (cuts19426.take 1).map (fun c => (2550136833-1+2*2^9*c.k,99643224434876+c.lower,99643604581469+c.upper)) = pointBounds19426 := by
 decide +kernel
def cuts19427 : List PrefixCut := [⟨16,85978514,85978565⟩,
⟨94,486615371,486615656⟩,
⟨128,663090299,663090686⟩]
theorem checked19427 : checkPrefixCuts (2^48) 2550267905 9 Manual.Count131072.C019427.packed 128 cuts19427 = true := by
 decide +kernel
def pointBounds19427 : List (Nat × Nat × Nat) := [(2550284288,99643983140146,99644363287189),(2550364160,99644383777003,99644763924280)]
theorem point_links_checked19427 : (cuts19427.take 2).map (fun c => (2550267905-1+2*2^9*c.k,99643897161632+c.lower,99644277308624+c.upper)) = pointBounds19427 := by
 decide +kernel
def cuts19428 : List PrefixCut := [⟨44,227129228,227129360⟩,
⟨122,636349187,636349560⟩,
⟨128,668022364,668022756⟩]
theorem checked19428 : checkPrefixCuts (2^48) 2550398977 9 Manual.Count131072.C019428.packed 128 cuts19428 = true := by
 decide +kernel
def pointBounds19428 : List (Nat × Nat × Nat) := [(2550444032,99644787381159,99645167528670),(2550523904,99645196601118,99645576748870)]
theorem point_links_checked19428 : (cuts19428.take 2).map (fun c => (2550398977-1+2*2^9*c.k,99644560251931+c.lower,99644940399310+c.upper)) = pointBounds19428 := by
 decide +kernel
def cuts19429 : List PrefixCut := [⟨72,376651135,376651357⟩,
⟨128,667546798,667547194⟩]
theorem checked19429 : checkPrefixCuts (2^48) 2550530049 9 Manual.Count131072.C019429.packed 128 cuts19429 = true := by
 decide +kernel
def pointBounds19429 : List (Nat × Nat × Nat) := [(2550603776,99645604925430,99645985073423)]
theorem point_links_checked19429 : (cuts19429.take 1).map (fun c => (2550530049-1+2*2^9*c.k,99645228274295+c.lower,99645608422066+c.upper)) = pointBounds19429 := by
 decide +kernel
def cuts19430 : List PrefixCut := [⟨22,116422634,116422704⟩,
⟨100,524169589,524169901⟩,
⟨128,673029920,673030323⟩]
theorem checked19430 : checkPrefixCuts (2^48) 2550661121 9 Manual.Count131072.C019430.packed 128 cuts19430 = true := by
 decide +kernel
def pointBounds19430 : List (Nat × Nat × Nat) := [(2550683648,99646012243727,99646392391964),(2550763520,99646419990682,99646800139161)]
theorem point_links_checked19430 : (cuts19430.take 2).map (fun c => (2550661121-1+2*2^9*c.k,99645895821093+c.lower,99646275969260+c.upper)) = pointBounds19430 := by
 decide +kernel
def cuts19431 : List PrefixCut := [⟨50,258873881,258874037⟩,
⟨128,659533269,659533664⟩]
theorem checked19431 : checkPrefixCuts (2^48) 2550792193 9 Manual.Count131072.C019431.packed 128 cuts19431 = true := by
 decide +kernel
def pointBounds19431 : List (Nat × Nat × Nat) := [(2550843392,99646827724894,99647207873620),(2550923264,99647228384282,99647608533247)]
theorem point_links_checked19431 : (cuts19431.take 2).map (fun c => (2550792193-1+2*2^9*c.k,99646568851013+c.lower,99646948999583+c.upper)) = pointBounds19431 := by
 decide +kernel
def cuts19432 : List PrefixCut := [⟨78,408481021,408481263⟩,
⟨128,666561143,666561541⟩]
theorem checked19432 : checkPrefixCuts (2^48) 2550923265 9 Manual.Count131072.C019432.packed 128 cuts19432 = true := by
 decide +kernel
def pointBounds19432 : List (Nat × Nat × Nat) := [(2551003136,99647636865303,99648017014510)]
theorem point_links_checked19432 : (cuts19432.take 1).map (fun c => (2550923265-1+2*2^9*c.k,99647228384282+c.lower,99647608533247+c.upper)) = pointBounds19432 := by
 decide +kernel
def cuts19433 : List PrefixCut := [⟨28,144760910,144760998⟩,
⟨106,546485960,546486288⟩,
⟨128,661782391,661782789⟩]
theorem checked19433 : checkPrefixCuts (2^48) 2551054337 9 Manual.Count131072.C019433.packed 128 cuts19433 = true := by
 decide +kernel
def pointBounds19433 : List (Nat × Nat × Nat) := [(2551083008,99648039706335,99648419855786),(2551162880,99648441431385,99648821581076)]
theorem point_links_checked19433 : (cuts19433.take 2).map (fun c => (2551054337-1+2*2^9*c.k,99647894945425+c.lower,99648275094788+c.upper)) = pointBounds19433 := by
 decide +kernel
def cuts19434 : List PrefixCut := [⟨56,291491273,291491448⟩,
⟨128,672560532,672560934⟩]
theorem checked19434 : checkPrefixCuts (2^48) 2551185409 9 Manual.Count131072.C019434.packed 128 cuts19434 = true := by
 decide +kernel
def pointBounds19434 : List (Nat × Nat × Nat) := [(2551242752,99648848219089,99649228369025)]
theorem point_links_checked19434 : (cuts19434.take 1).map (fun c => (2551185409-1+2*2^9*c.k,99648556727816+c.lower,99648936877577+c.upper)) = pointBounds19434 := by
 decide +kernel
def cuts19435 : List PrefixCut := [⟨6,31332365,31332383⟩,
⟨84,432247432,432247689⟩,
⟨128,657191272,657191661⟩]
theorem checked19435 : checkPrefixCuts (2^48) 2551316481 9 Manual.Count131072.C019435.packed 128 cuts19435 = true := by
 decide +kernel
def pointBounds19435 : List (Nat × Nat × Nat) := [(2551322624,99649260620713,99649640770894),(2551402496,99649661535780,99650041686200)]
theorem point_links_checked19435 : (cuts19435.take 2).map (fun c => (2551316481-1+2*2^9*c.k,99649229288348+c.lower,99649609438511+c.upper)) = pointBounds19435 := by
 decide +kernel
def cuts19436 : List PrefixCut := [⟨34,184784223,184784329⟩,
⟨112,585894808,585895154⟩,
⟨128,669844044,669844440⟩]
theorem checked19436 : checkPrefixCuts (2^48) 2551447553 9 Manual.Count131072.C019436.packed 128 cuts19436 = true := by
 decide +kernel
def pointBounds19436 : List (Nat × Nat × Nat) := [(2551482368,99650071263843,99650451414501),(2551562240,99650472374428,99650852525326)]
theorem point_links_checked19436 : (cuts19436.take 2).map (fun c => (2551447553-1+2*2^9*c.k,99649886479620+c.lower,99650266630172+c.upper)) = pointBounds19436 := by
 decide +kernel
def cuts19437 : List PrefixCut := [⟨62,321340721,321340912⟩,
⟨128,673559976,673560376⟩]
theorem checked19437 : checkPrefixCuts (2^48) 2551578625 9 Manual.Count131072.C019437.packed 128 cuts19437 = true := by
 decide +kernel
def pointBounds19437 : List (Nat × Nat × Nat) := [(2551642112,99650877664385,99651257815524)]
theorem point_links_checked19437 : (cuts19437.take 1).map (fun c => (2551578625-1+2*2^9*c.k,99650556323664+c.lower,99650936474612+c.upper)) = pointBounds19437 := by
 decide +kernel
def cuts19438 : List PrefixCut := [⟨12,62875612,62875648⟩,
⟨90,463838263,463838539⟩,
⟨128,664149498,664149889⟩]
theorem checked19438 : checkPrefixCuts (2^48) 2551709697 9 Manual.Count131072.C019438.packed 128 cuts19438 = true := by
 decide +kernel
def pointBounds19438 : List (Nat × Nat × Nat) := [(2551721984,99651292759252,99651672910636),(2551801856,99651693721903,99652073873527)]
theorem point_links_checked19438 : (cuts19438.take 2).map (fun c => (2551709697-1+2*2^9*c.k,99651229883640+c.lower,99651610034988+c.upper)) = pointBounds19438 := by
 decide +kernel
def cuts19439 : List PrefixCut := [⟨40,209132204,209132327⟩,
⟨118,619003999,619004366⟩,
⟨128,671836375,671836773⟩]
theorem checked19439 : checkPrefixCuts (2^48) 2551840769 9 Manual.Count131072.C019439.packed 128 cuts19439 = true := by
 decide +kernel
def pointBounds19439 : List (Nat × Nat × Nat) := [(2551881728,99652103165342,99652483317204),(2551961600,99652513037137,99652893189243)]
theorem point_links_checked19439 : (cuts19439.take 2).map (fun c => (2551840769-1+2*2^9*c.k,99651894033138+c.lower,99652274184877+c.upper)) = pointBounds19439 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000294
