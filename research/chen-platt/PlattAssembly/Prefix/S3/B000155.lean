import PlattAssemblyKernel
import PlattCertificates.Count131072.C024960
import PlattCertificates.Count131072.C024961
import PlattCertificates.Count131072.C024962
import PlattCertificates.Count131072.C024963
import PlattCertificates.Count131072.C024964
import PlattCertificates.Count131072.C024965
import PlattCertificates.Count131072.C024966
import PlattCertificates.Count131072.C024967
import PlattCertificates.Count131072.C024968
import PlattCertificates.Count131072.C024969
import PlattCertificates.Count131072.C024970
import PlattCertificates.Count131072.C024971
import PlattCertificates.Count131072.C024972
import PlattCertificates.Count131072.C024973
import PlattCertificates.Count131072.C024974
import PlattCertificates.Count131072.C024975
import PlattCertificates.Count131072.C024976
import PlattCertificates.Count131072.C024977
import PlattCertificates.Count131072.C024978
import PlattCertificates.Count131072.C024979
import PlattCertificates.Count131072.C024980
import PlattCertificates.Count131072.C024981
import PlattCertificates.Count131072.C024982
import PlattCertificates.Count131072.C024983
import PlattCertificates.Count131072.C024984
import PlattCertificates.Count131072.C024985
import PlattCertificates.Count131072.C024986
import PlattCertificates.Count131072.C024987
import PlattCertificates.Count131072.C024988
import PlattCertificates.Count131072.C024989
import PlattCertificates.Count131072.C024990
import PlattCertificates.Count131072.C024991
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000155
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts24960 : List PrefixCut := [⟨43,176678490,176678590⟩,
⟨128,523669463,523669757⟩]
theorem checked24960 : checkPrefixCuts (2^48) 3275489281 9 Manual.Count131072.C024960.packed 128 cuts24960 = true := by
 decide +kernel
def pointBounds24960 : List (Nat × Nat × Nat) := [(3275533312,102877614299421,102877996304468)]
theorem point_links_checked24960 : (cuts24960.take 1).map (fun c => (3275489281-1+2*2^9*c.k,102877437620931+c.lower,102877819625878+c.upper)) = pointBounds24960 := by
 decide +kernel
def cuts24961 : List PrefixCut := [⟨15,60924412,60924446⟩,
⟨115,459804505,459804769⟩,
⟨128,512391823,512392118⟩]
theorem checked24961 : checkPrefixCuts (2^48) 3275620353 9 Manual.Count131072.C024961.packed 128 cuts24961 = true := by
 decide +kernel
def pointBounds24961 : List (Nat × Nat × Nat) := [(3275635712,102878022214806,102878404220081),(3275738112,102878421094899,102878803100404)]
theorem point_links_checked24961 : (cuts24961.take 2).map (fun c => (3275620353-1+2*2^9*c.k,102877961290394+c.lower,102878343295635+c.upper)) = pointBounds24961 := by
 decide +kernel
def cuts24962 : List PrefixCut := [⟨87,346452257,346452456⟩,
⟨128,510910665,510910958⟩]
theorem checked24962 : checkPrefixCuts (2^48) 3275751425 9 Manual.Count131072.C024962.packed 128 cuts24962 = true := by
 decide +kernel
def pointBounds24962 : List (Nat × Nat × Nat) := [(3275840512,102878820134474,102879202140209)]
theorem point_links_checked24962 : (cuts24962.take 1).map (fun c => (3275751425-1+2*2^9*c.k,102878473682217+c.lower,102878855687753+c.upper)) = pointBounds24962 := by
 decide +kernel
def cuts24963 : List PrefixCut := [⟨59,240755113,240755250⟩,
⟨128,522661482,522661777⟩]
theorem checked24963 : checkPrefixCuts (2^48) 3275882497 9 Manual.Count131072.C024963.packed 128 cuts24963 = true := by
 decide +kernel
def pointBounds24963 : List (Nat × Nat × Nat) := [(3275942912,102879225347995,102879607353961)]
theorem point_links_checked24963 : (cuts24963.take 1).map (fun c => (3275882497-1+2*2^9*c.k,102878984592882+c.lower,102879366598711+c.upper)) = pointBounds24963 := by
 decide +kernel
def cuts24964 : List PrefixCut := [⟨31,128363769,128363841⟩,
⟨128,515767145,515767438⟩]
theorem checked24964 : checkPrefixCuts (2^48) 3276013569 9 Manual.Count131072.C024964.packed 128 cuts24964 = true := by
 decide +kernel
def pointBounds24964 : List (Nat × Nat × Nat) := [(3276045312,102879635618133,102880017624329)]
theorem point_links_checked24964 : (cuts24964.take 1).map (fun c => (3276013569-1+2*2^9*c.k,102879507254364+c.lower,102879889260488+c.upper)) = pointBounds24964 := by
 decide +kernel
def cuts24965 : List PrefixCut := [⟨3,11169140,11169146⟩,
⟨103,410674267,410674497⟩,
⟨128,507928243,507928526⟩]
theorem checked24965 : checkPrefixCuts (2^48) 3276144641 9 Manual.Count131072.C024965.packed 128 cuts24965 = true := by
 decide +kernel
def pointBounds24965 : List (Nat × Nat × Nat) := [(3276147712,102880034190649,102880416197072),(3276250112,102880433695776,102880815702423)]
theorem point_links_checked24965 : (cuts24965.take 2).map (fun c => (3276144641-1+2*2^9*c.k,102880023021509+c.lower,102880405027926+c.upper)) = pointBounds24965 := by
 decide +kernel
def cuts24966 : List PrefixCut := [⟨75,304472338,304472505⟩,
⟨128,518131374,518131658⟩]
theorem checked24966 : checkPrefixCuts (2^48) 3276275713 9 Manual.Count131072.C024966.packed 128 cuts24966 = true := by
 decide +kernel
def pointBounds24966 : List (Nat × Nat × Nat) := [(3276352512,102880835422090,102881217428957)]
theorem point_links_checked24966 : (cuts24966.take 1).map (fun c => (3276275713-1+2*2^9*c.k,102880530949752+c.lower,102880912956452+c.upper)) = pointBounds24966 := by
 decide +kernel
def cuts24967 : List PrefixCut := [⟨47,189429353,189429460⟩,
⟨128,520430040,520430332⟩]
theorem checked24967 : checkPrefixCuts (2^48) 3276406785 9 Manual.Count131072.C024967.packed 128 cuts24967 = true := by
 decide +kernel
def pointBounds24967 : List (Nat × Nat × Nat) := [(3276454912,102881238510479,102881620517570)]
theorem point_links_checked24967 : (cuts24967.take 1).map (fun c => (3276406785-1+2*2^9*c.k,102881049081126+c.lower,102881431088110+c.upper)) = pointBounds24967 := by
 decide +kernel
def cuts24968 : List PrefixCut := [⟨19,76026760,76026805⟩,
⟨119,479519475,479519742⟩,
⟨128,516457711,516457998⟩]
theorem checked24968 : checkPrefixCuts (2^48) 3276537857 9 Manual.Count131072.C024968.packed 128 cuts24968 = true := by
 decide +kernel
def pointBounds24968 : List (Nat × Nat × Nat) := [(3276557312,102881645537926,102882027545247),(3276659712,102882049030641,102882431038184)]
theorem point_links_checked24968 : (cuts24968.take 2).map (fun c => (3276537857-1+2*2^9*c.k,102881569511166+c.lower,102881951518442+c.upper)) = pointBounds24968 := by
 decide +kernel
def cuts24969 : List PrefixCut := [⟨91,359755651,359755850⟩,
⟨128,508104645,508104930⟩]
theorem checked24969 : checkPrefixCuts (2^48) 3276668929 9 Manual.Count131072.C024969.packed 128 cuts24969 = true := by
 decide +kernel
def pointBounds24969 : List (Nat × Nat × Nat) := [(3276762112,102882445724528,102882827732290)]
theorem point_links_checked24969 : (cuts24969.take 1).map (fun c => (3276668929-1+2*2^9*c.k,102882085968877+c.lower,102882467976440+c.upper)) = pointBounds24969 := by
 decide +kernel
def cuts24970 : List PrefixCut := [⟨63,253915924,253916069⟩,
⟨128,514183099,514183388⟩]
theorem checked24970 : checkPrefixCuts (2^48) 3276800001 9 Manual.Count131072.C024970.packed 128 cuts24970 = true := by
 decide +kernel
def pointBounds24970 : List (Nat × Nat × Nat) := [(3276864512,102882847989446,102883229997439)]
theorem point_links_checked24970 : (cuts24970.take 1).map (fun c => (3276800001-1+2*2^9*c.k,102882594073522+c.lower,102882976081370+c.upper)) = pointBounds24970 := by
 decide +kernel
def cuts24971 : List PrefixCut := [⟨36,147568315,147568395⟩,
⟨128,508407681,508407966⟩]
theorem checked24971 : checkPrefixCuts (2^48) 3276931073 9 Manual.Count131072.C024971.packed 128 cuts24971 = true := by
 decide +kernel
def pointBounds24971 : List (Nat × Nat × Nat) := [(3276967936,102883255824936,102883637833153)]
theorem point_links_checked24971 : (cuts24971.take 1).map (fun c => (3276931073-1+2*2^9*c.k,102883108256621+c.lower,102883490264758+c.upper)) = pointBounds24971 := by
 decide +kernel
def cuts24972 : List PrefixCut := [⟨9,38136195,38136216⟩,
⟨110,446804840,446805090⟩,
⟨128,518436481,518436772⟩]
theorem checked24972 : checkPrefixCuts (2^48) 3277062145 9 Manual.Count131072.C024972.packed 128 cuts24972 = true := by
 decide +kernel
def pointBounds24972 : List (Nat × Nat × Nat) := [(3277071360,102883654800497,102884036808940),(3277174784,102884063469142,102884445477814)]
theorem point_links_checked24972 : (cuts24972.take 2).map (fun c => (3277062145-1+2*2^9*c.k,102883616664302+c.lower,102883998672724+c.upper)) = pointBounds24972 := by
 decide +kernel
def cuts24973 : List PrefixCut := [⟨83,334791010,334791194⟩,
⟨128,518329773,518330060⟩]
theorem checked24973 : checkPrefixCuts (2^48) 3277193217 9 Manual.Count131072.C024973.packed 128 cuts24973 = true := by
 decide +kernel
def pointBounds24973 : List (Nat × Nat × Nat) := [(3277278208,102884469891793,102884851900690)]
theorem point_links_checked24973 : (cuts24973.take 1).map (fun c => (3277193217-1+2*2^9*c.k,102884135100783+c.lower,102884517109496+c.upper)) = pointBounds24973 := by
 decide +kernel
def cuts24974 : List PrefixCut := [⟨56,226564204,226564328⟩,
⟨128,516333792,516334077⟩]
theorem checked24974 : checkPrefixCuts (2^48) 3277324289 9 Manual.Count131072.C024974.packed 128 cuts24974 = true := by
 decide +kernel
def pointBounds24974 : List (Nat × Nat × Nat) := [(3277381632,102884879994760,102885262003884)]
theorem point_links_checked24974 : (cuts24974.take 1).map (fun c => (3277324289-1+2*2^9*c.k,102884653430556+c.lower,102885035439556+c.upper)) = pointBounds24974 := by
 decide +kernel
def cuts24975 : List PrefixCut := [⟨29,114738028,114738093⟩,
⟨128,510129696,510129996⟩]
theorem checked24975 : checkPrefixCuts (2^48) 3277455361 9 Manual.Count131072.C024975.packed 128 cuts24975 = true := by
 decide +kernel
def pointBounds24975 : List (Nat × Nat × Nat) := [(3277485056,102885284502376,102885666511726)]
theorem point_links_checked24975 : (cuts24975.take 1).map (fun c => (3277455361-1+2*2^9*c.k,102885169764348+c.lower,102885551773633+c.upper)) = pointBounds24975 := by
 decide +kernel
def cuts24976 : List PrefixCut := [⟨2,7471446,7471450⟩,
⟨103,409463130,409463358⟩,
⟨128,511569234,511569516⟩]
theorem checked24976 : checkPrefixCuts (2^48) 3277586433 9 Manual.Count131072.C024976.packed 128 cuts24976 = true := by
 decide +kernel
def pointBounds24976 : List (Nat × Nat × Nat) := [(3277588480,102885687365490,102886069375079),(3277691904,102886089357174,102886471366987)]
theorem point_links_checked24976 : (cuts24976.take 2).map (fun c => (3277586433-1+2*2^9*c.k,102885679894044+c.lower,102886061903629+c.upper)) = pointBounds24976 := by
 decide +kernel
def cuts24977 : List PrefixCut := [⟨76,303050281,303050450⟩,
⟨128,517216394,517216684⟩]
theorem checked24977 : checkPrefixCuts (2^48) 3277717505 9 Manual.Count131072.C024977.packed 128 cuts24977 = true := by
 decide +kernel
def pointBounds24977 : List (Nat × Nat × Nat) := [(3277795328,102886494513559,102886876523595)]
theorem point_links_checked24977 : (cuts24977.take 1).map (fun c => (3277717505-1+2*2^9*c.k,102886191463278+c.lower,102886573473145+c.upper)) = pointBounds24977 := by
 decide +kernel
def cuts24978 : List PrefixCut := [⟨49,202484255,202484366⟩,
⟨128,519170827,519171114⟩]
theorem checked24978 : checkPrefixCuts (2^48) 3277848577 9 Manual.Count131072.C024978.packed 128 cuts24978 = true := by
 decide +kernel
def pointBounds24978 : List (Nat × Nat × Nat) := [(3277898752,102886911163927,102887293174195)]
theorem point_links_checked24978 : (cuts24978.take 1).map (fun c => (3277848577-1+2*2^9*c.k,102886708679672+c.lower,102887090689829+c.upper)) = pointBounds24978 := by
 decide +kernel
def cuts24979 : List PrefixCut := [⟨22,83979008,83979058⟩,
⟨123,485147144,485147424⟩,
⟨128,504466778,504467070⟩]
theorem checked24979 : checkPrefixCuts (2^48) 3277979649 9 Manual.Count131072.C024979.packed 128 cuts24979 = true := by
 decide +kernel
def pointBounds24979 : List (Nat × Nat × Nat) := [(3278002176,102887311829507,102887693840001),(3278105600,102887712997643,102888095008367)]
theorem point_links_checked24979 : (cuts24979.take 2).map (fun c => (3277979649-1+2*2^9*c.k,102887227850499+c.lower,102887609860943+c.upper)) = pointBounds24979 := by
 decide +kernel
def cuts24980 : List PrefixCut := [⟨96,392053609,392053828⟩,
⟨128,522134490,522134783⟩]
theorem checked24980 : checkPrefixCuts (2^48) 3278110721 9 Manual.Count131072.C024980.packed 128 cuts24980 = true := by
 decide +kernel
def pointBounds24980 : List (Nat × Nat × Nat) := [(3278209024,102888124370886,102888506381841)]
theorem point_links_checked24980 : (cuts24980.take 1).map (fun c => (3278110721-1+2*2^9*c.k,102887732317277+c.lower,102888114328013+c.upper)) = pointBounds24980 := by
 decide +kernel
def cuts24981 : List PrefixCut := [⟨69,273981217,273981365⟩,
⟨128,513441692,513441976⟩]
theorem checked24981 : checkPrefixCuts (2^48) 3278241793 9 Manual.Count131072.C024981.packed 128 cuts24981 = true := by
 decide +kernel
def pointBounds24981 : List (Nat × Nat × Nat) := [(3278312448,102888528432984,102888910444161)]
theorem point_links_checked24981 : (cuts24981.take 1).map (fun c => (3278241793-1+2*2^9*c.k,102888254451767+c.lower,102888636462796+c.upper)) = pointBounds24981 := by
 decide +kernel
def cuts24982 : List PrefixCut := [⟨42,169482792,169482887⟩,
⟨128,514537396,514537680⟩]
theorem checked24982 : checkPrefixCuts (2^48) 3278372865 9 Manual.Count131072.C024982.packed 128 cuts24982 = true := by
 decide +kernel
def pointBounds24982 : List (Nat × Nat × Nat) := [(3278415872,102888937376251,102889319387659)]
theorem point_links_checked24982 : (cuts24982.take 1).map (fun c => (3278372865-1+2*2^9*c.k,102888767893459+c.lower,102889149904772+c.upper)) = pointBounds24982 := by
 decide +kernel
def cuts24983 : List PrefixCut := [⟨15,58466894,58466929⟩,
⟨116,466611646,466611917⟩,
⟨128,514173324,514173623⟩]
theorem checked24983 : checkPrefixCuts (2^48) 3278503937 9 Manual.Count131072.C024983.packed 128 cuts24983 = true := by
 decide +kernel
def pointBounds24983 : List (Nat × Nat × Nat) := [(3278519296,102889340897749,102889722909381),(3278622720,102889749042501,102890131054369)]
theorem point_links_checked24983 : (cuts24983.take 2).map (fun c => (3278503937-1+2*2^9*c.k,102889282430855+c.lower,102889664442452+c.upper)) = pointBounds24983 := by
 decide +kernel
def cuts24984 : List PrefixCut := [⟨89,354388984,354389183⟩,
⟨128,512435770,512436054⟩]
theorem checked24984 : checkPrefixCuts (2^48) 3278635009 9 Manual.Count131072.C024984.packed 128 cuts24984 = true := by
 decide +kernel
def pointBounds24984 : List (Nat × Nat × Nat) := [(3278726144,102890150993163,102890533005258)]
theorem point_links_checked24984 : (cuts24984.take 1).map (fun c => (3278635009-1+2*2^9*c.k,102889796604179+c.lower,102890178616075+c.upper)) = pointBounds24984 := by
 decide +kernel
def cuts24985 : List PrefixCut := [⟨62,245694091,245694231⟩,
⟨128,507007086,507007377⟩]
theorem checked24985 : checkPrefixCuts (2^48) 3278766081 9 Manual.Count131072.C024985.packed 128 cuts24985 = true := by
 decide +kernel
def pointBounds24985 : List (Nat × Nat × Nat) := [(3278829568,102890554734040,102890936746360)]
theorem point_links_checked24985 : (cuts24985.take 1).map (fun c => (3278766081-1+2*2^9*c.k,102890309039949+c.lower,102890691052129+c.upper)) = pointBounds24985 := by
 decide +kernel
def cuts24986 : List PrefixCut := [⟨35,140440636,140440713⟩,
⟨128,513424987,513425273⟩]
theorem checked24986 : checkPrefixCuts (2^48) 3278897153 9 Manual.Count131072.C024986.packed 128 cuts24986 = true := by
 decide +kernel
def pointBounds24986 : List (Nat × Nat × Nat) := [(3278932992,102890956487671,102891338500219)]
theorem point_links_checked24986 : (cuts24986.take 1).map (fun c => (3278897153-1+2*2^9*c.k,102890816047035+c.lower,102891198059506+c.upper)) = pointBounds24986 := by
 decide +kernel
def cuts24987 : List PrefixCut := [⟨8,33048725,33048744⟩,
⟨109,434862862,434863109⟩,
⟨128,511601829,511602118⟩]
theorem checked24987 : checkPrefixCuts (2^48) 3279028225 9 Manual.Count131072.C024987.packed 128 cuts24987 = true := by
 decide +kernel
def pointBounds24987 : List (Nat × Nat × Nat) := [(3279036416,102891362520747,102891744533523),(3279139840,102891764334884,102892146347888)]
theorem point_links_checked24987 : (cuts24987.take 2).map (fun c => (3279028225-1+2*2^9*c.k,102891329472022+c.lower,102891711484779+c.upper)) = pointBounds24987 := by
 decide +kernel
def cuts24988 : List PrefixCut := [⟨82,330727703,330727885⟩,
⟨128,514499814,514500099⟩]
theorem checked24988 : checkPrefixCuts (2^48) 3279159297 9 Manual.Count131072.C024988.packed 128 cuts24988 = true := by
 decide +kernel
def pointBounds24988 : List (Nat × Nat × Nat) := [(3279243264,102892171801554,102892553814782)]
theorem point_links_checked24988 : (cuts24988.take 1).map (fun c => (3279159297-1+2*2^9*c.k,102891841073851+c.lower,102892223086897+c.upper)) = pointBounds24988 := by
 decide +kernel
def cuts24989 : List PrefixCut := [⟨55,219905032,219905156⟩,
⟨128,517912394,517912680⟩]
theorem checked24989 : checkPrefixCuts (2^48) 3279290369 9 Manual.Count131072.C024989.packed 128 cuts24989 = true := by
 decide +kernel
def pointBounds24989 : List (Nat × Nat × Nat) := [(3279346688,102892575478697,102892957492152)]
theorem point_links_checked24989 : (cuts24989.take 1).map (fun c => (3279290369-1+2*2^9*c.k,102892355573665+c.lower,102892737586996+c.upper)) = pointBounds24989 := by
 decide +kernel
def cuts24990 : List PrefixCut := [⟨28,112695152,112695217⟩,
⟨128,518235128,518235415⟩]
theorem checked24990 : checkPrefixCuts (2^48) 3279421441 9 Manual.Count131072.C024990.packed 128 cuts24990 = true := by
 decide +kernel
def pointBounds24990 : List (Nat × Nat × Nat) := [(3279450112,102892986181211,102893368194893)]
theorem point_links_checked24990 : (cuts24990.take 1).map (fun c => (3279421441-1+2*2^9*c.k,102892873486059+c.lower,102893255499676+c.upper)) = pointBounds24990 := by
 decide +kernel
def cuts24991 : List PrefixCut := [⟨1,4720497,4720499⟩,
⟨102,411706635,411706871⟩,
⟨128,513923190,513923484⟩]
theorem checked24991 : checkPrefixCuts (2^48) 3279552513 9 Manual.Count131072.C024991.packed 128 cuts24991 = true := by
 decide +kernel
def pointBounds24991 : List (Nat × Nat × Nat) := [(3279553536,102893396441684,102893778455590),(3279656960,102893803427822,102894185441962)]
theorem point_links_checked24991 : (cuts24991.take 2).map (fun c => (3279552513-1+2*2^9*c.k,102893391721187+c.lower,102893773735091+c.upper)) = pointBounds24991 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000155
