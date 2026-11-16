import PlattAssemblyKernel
import PlattCertificates.Count131072.C030288
import PlattCertificates.Count131072.C030289
import PlattCertificates.Count131072.C030290
import PlattCertificates.Count131072.C030291
import PlattCertificates.Count131072.C030292
import PlattCertificates.Count131072.C030293
import PlattCertificates.Count131072.C030294
import PlattCertificates.Count131072.C030295
import PlattCertificates.Count131072.C030296
import PlattCertificates.Count131072.C030297
import PlattCertificates.Count131072.C030298
import PlattCertificates.Count131072.C030299
import PlattCertificates.Count131072.C030300
import PlattCertificates.Count131072.C030301
import PlattCertificates.Count131072.C030302
import PlattCertificates.Count131072.C030303
import PlattCertificates.Count131072.C030304
import PlattCertificates.Count131072.C030305
import PlattCertificates.Count131072.C030306
import PlattCertificates.Count131072.C030307
import PlattCertificates.Count131072.C030308
import PlattCertificates.Count131072.C030309
import PlattCertificates.Count131072.C030310
import PlattCertificates.Count131072.C030311
import PlattCertificates.Count131072.C030312
import PlattCertificates.Count131072.C030313
import PlattCertificates.Count131072.C030314
import PlattCertificates.Count131072.C030315
import PlattCertificates.Count131072.C030316
import PlattCertificates.Count131072.C030317
import PlattCertificates.Count131072.C030318
import PlattCertificates.Count131072.C030319
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000009
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts30288 : List PrefixCut := [⟨117,381424290,381424501⟩,
⟨128,416768314,416768546⟩]
theorem checked30288 : checkPrefixCuts (2^48) 3973840897 9 Manual.Count131072.C030288.packed 128 cuts30288 = true := by
 decide +kernel
def pointBounds30288 : List (Nat × Nat × Nat) := [(3973960704,105349954826739,105350338216568)]
theorem point_links_checked30288 : (cuts30288.take 1).map (fun c => (3973840897-1+2*2^9*c.k,105349573402449+c.lower,105349956792067+c.upper)) = pointBounds30288 := by
 decide +kernel
def cuts30289 : List PrefixCut := [⟨111,361863347,361863551⟩,
⟨128,418454463,418454700⟩]
theorem checked30289 : checkPrefixCuts (2^48) 3973971969 9 Manual.Count131072.C030289.packed 128 cuts30289 = true := by
 decide +kernel
def pointBounds30289 : List (Nat × Nat × Nat) := [(3974085632,105350352034110,105350735424164)]
theorem point_links_checked30289 : (cuts30289.take 1).map (fun c => (3973971969-1+2*2^9*c.k,105349990170763+c.lower,105350373560613+c.upper)) = pointBounds30289 := by
 decide +kernel
def cuts30290 : List PrefixCut := [⟨105,345703257,345703455⟩,
⟨128,422690196,422690439⟩]
theorem checked30290 : checkPrefixCuts (2^48) 3974103041 9 Manual.Count131072.C030290.packed 128 cuts30290 = true := by
 decide +kernel
def pointBounds30290 : List (Nat × Nat × Nat) := [(3974210560,105350754328483,105351137718768)]
theorem point_links_checked30290 : (cuts30290.take 1).map (fun c => (3974103041-1+2*2^9*c.k,105350408625226+c.lower,105350792015313+c.upper)) = pointBounds30290 := by
 decide +kernel
def cuts30291 : List PrefixCut := [⟨99,325082319,325082499⟩,
⟨128,418214389,418214622⟩]
theorem checked30291 : checkPrefixCuts (2^48) 3974234113 9 Manual.Count131072.C030291.packed 128 cuts30291 = true := by
 decide +kernel
def pointBounds30291 : List (Nat × Nat × Nat) := [(3974335488,105351156397741,105351539788251)]
theorem point_links_checked30291 : (cuts30291.take 1).map (fun c => (3974234113-1+2*2^9*c.k,105350831315422+c.lower,105351214705752+c.upper)) = pointBounds30291 := by
 decide +kernel
def cuts30292 : List PrefixCut := [⟨93,308995275,308995450⟩,
⟨128,421316731,421316968⟩]
theorem checked30292 : checkPrefixCuts (2^48) 3974365185 9 Manual.Count131072.C030292.packed 128 cuts30292 = true := by
 decide +kernel
def pointBounds30292 : List (Nat × Nat × Nat) := [(3974460416,105351558525086,105351941915824)]
theorem point_links_checked30292 : (cuts30292.take 1).map (fun c => (3974365185-1+2*2^9*c.k,105351249529811+c.lower,105351632920374+c.upper)) = pointBounds30292 := by
 decide +kernel
def cuts30293 : List PrefixCut := [⟨87,284765134,284765291⟩,
⟨128,416841274,416841508⟩]
theorem checked30293 : checkPrefixCuts (2^48) 3974496257 9 Manual.Count131072.C030293.packed 128 cuts30293 = true := by
 decide +kernel
def pointBounds30293 : List (Nat × Nat × Nat) := [(3974585344,105351955611676,105352339002633)]
theorem point_links_checked30293 : (cuts30293.take 1).map (fun c => (3974496257-1+2*2^9*c.k,105351670846542+c.lower,105352054237342+c.upper)) = pointBounds30293 := by
 decide +kernel
def cuts30294 : List PrefixCut := [⟨81,270380065,270380218⟩,
⟨128,423201053,423201297⟩]
theorem checked30294 : checkPrefixCuts (2^48) 3974627329 9 Manual.Count131072.C030294.packed 128 cuts30294 = true := by
 decide +kernel
def pointBounds30294 : List (Nat × Nat × Nat) := [(3974710272,105352358067881,105352741459068)]
theorem point_links_checked30294 : (cuts30294.take 1).map (fun c => (3974627329-1+2*2^9*c.k,105352087687816+c.lower,105352471078850+c.upper)) = pointBounds30294 := by
 decide +kernel
def cuts30295 : List PrefixCut := [⟨75,246577526,246577665⟩,
⟨128,422762129,422762370⟩]
theorem checked30295 : checkPrefixCuts (2^48) 3974758401 9 Manual.Count131072.C030295.packed 128 cuts30295 = true := by
 decide +kernel
def pointBounds30295 : List (Nat × Nat × Nat) := [(3974835200,105352757466395,105353140857812)]
theorem point_links_checked30295 : (cuts30295.take 1).map (fun c => (3974758401-1+2*2^9*c.k,105352510888869+c.lower,105352894280147+c.upper)) = pointBounds30295 := by
 decide +kernel
def cuts30296 : List PrefixCut := [⟨69,228724807,228724939⟩,
⟨128,423314708,423314946⟩]
theorem checked30296 : checkPrefixCuts (2^48) 3974889473 9 Manual.Count131072.C030296.packed 128 cuts30296 = true := by
 decide +kernel
def pointBounds30296 : List (Nat × Nat × Nat) := [(3974960128,105353162375805,105353545767456)]
theorem point_links_checked30296 : (cuts30296.take 1).map (fun c => (3974889473-1+2*2^9*c.k,105352933650998+c.lower,105353317042517+c.upper)) = pointBounds30296 := by
 decide +kernel
def cuts30297 : List PrefixCut := [⟨63,204641919,204642037⟩,
⟨128,416361428,416361664⟩]
theorem checked30297 : checkPrefixCuts (2^48) 3975020545 9 Manual.Count131072.C030297.packed 128 cuts30297 = true := by
 decide +kernel
def pointBounds30297 : List (Nat × Nat × Nat) := [(3975085056,105353561607625,105353944999500)]
theorem point_links_checked30297 : (cuts30297.take 1).map (fun c => (3975020545-1+2*2^9*c.k,105353356965706+c.lower,105353740357463+c.upper)) = pointBounds30297 := by
 decide +kernel
def cuts30298 : List PrefixCut := [⟨57,187712181,187712290⟩,
⟨128,421374976,421375218⟩]
theorem checked30298 : checkPrefixCuts (2^48) 3975151617 9 Manual.Count131072.C030298.packed 128 cuts30298 = true := by
 decide +kernel
def pointBounds30298 : List (Nat × Nat × Nat) := [(3975209984,105353961039315,105354344431417)]
theorem point_links_checked30298 : (cuts30298.take 1).map (fun c => (3975151617-1+2*2^9*c.k,105353773327134+c.lower,105354156719127+c.upper)) = pointBounds30298 := by
 decide +kernel
def cuts30299 : List PrefixCut := [⟨51,164340243,164340337⟩,
⟨128,416546309,416546541⟩]
theorem checked30299 : checkPrefixCuts (2^48) 3975282689 9 Manual.Count131072.C030299.packed 128 cuts30299 = true := by
 decide +kernel
def pointBounds30299 : List (Nat × Nat × Nat) := [(3975334912,105354359042353,105354742434682)]
theorem point_links_checked30299 : (cuts30299.take 1).map (fun c => (3975282689-1+2*2^9*c.k,105354194702110+c.lower,105354578094345+c.upper)) = pointBounds30299 := by
 decide +kernel
def cuts30300 : List PrefixCut := [⟨45,149183012,149183097⟩,
⟨128,424604155,424604392⟩]
theorem checked30300 : checkPrefixCuts (2^48) 3975413761 9 Manual.Count131072.C030300.packed 128 cuts30300 = true := by
 decide +kernel
def pointBounds30300 : List (Nat × Nat × Nat) := [(3975459840,105354760431431,105355143823983)]
theorem point_links_checked30300 : (cuts30300.take 1).map (fun c => (3975413761-1+2*2^9*c.k,105354611248419+c.lower,105354994640886+c.upper)) = pointBounds30300 := by
 decide +kernel
def cuts30301 : List PrefixCut := [⟨39,123618954,123619021⟩,
⟨128,418996814,418997046⟩]
theorem checked30301 : checkPrefixCuts (2^48) 3975544833 9 Manual.Count131072.C030301.packed 128 cuts30301 = true := by
 decide +kernel
def pointBounds30301 : List (Nat × Nat × Nat) := [(3975584768,105355159471528,105355542864299)]
theorem point_links_checked30301 : (cuts30301.take 1).map (fun c => (3975544833-1+2*2^9*c.k,105355035852574+c.lower,105355419245278+c.upper)) = pointBounds30301 := by
 decide +kernel
def cuts30302 : List PrefixCut := [⟨33,108817988,108818050⟩,
⟨128,412398896,412399127⟩]
theorem checked30302 : checkPrefixCuts (2^48) 3975675905 9 Manual.Count131072.C030302.packed 128 cuts30302 = true := by
 decide +kernel
def pointBounds30302 : List (Nat × Nat × Nat) := [(3975709696,105355563667376,105355947060374)]
theorem point_links_checked30302 : (cuts30302.take 1).map (fun c => (3975675905-1+2*2^9*c.k,105355454849388+c.lower,105355838242324+c.upper)) = pointBounds30302 := by
 decide +kernel
def cuts30303 : List PrefixCut := [⟨27,86867518,86867568⟩,
⟨128,421093091,421093329⟩]
theorem checked30303 : checkPrefixCuts (2^48) 3975806977 9 Manual.Count131072.C030303.packed 128 cuts30303 = true := by
 decide +kernel
def pointBounds30303 : List (Nat × Nat × Nat) := [(3975834624,105355954115802,105356337509019)]
theorem point_links_checked30303 : (cuts30303.take 1).map (fun c => (3975806977-1+2*2^9*c.k,105355867248284+c.lower,105356250641451+c.upper)) = pointBounds30303 := by
 decide +kernel
def cuts30304 : List PrefixCut := [⟨21,67042296,67042334⟩,
⟨128,425539168,425539404⟩]
theorem checked30304 : checkPrefixCuts (2^48) 3975938049 9 Manual.Count131072.C030304.packed 128 cuts30304 = true := by
 decide +kernel
def pointBounds30304 : List (Nat × Nat × Nat) := [(3975959552,105356355383671,105356738777114)]
theorem point_links_checked30304 : (cuts30304.take 1).map (fun c => (3975938049-1+2*2^9*c.k,105356288341375+c.lower,105356671734780+c.upper)) = pointBounds30304 := by
 decide +kernel
def cuts30305 : List PrefixCut := [⟨15,50120818,50120847⟩,
⟨128,417950638,417950875⟩]
theorem checked30305 : checkPrefixCuts (2^48) 3976069121 9 Manual.Count131072.C030305.packed 128 cuts30305 = true := by
 decide +kernel
def pointBounds30305 : List (Nat × Nat × Nat) := [(3976084480,105356764001361,105357147395031)]
theorem point_links_checked30305 : (cuts30305.take 1).map (fun c => (3976069121-1+2*2^9*c.k,105356713880543+c.lower,105357097274184+c.upper)) = pointBounds30305 := by
 decide +kernel
def cuts30306 : List PrefixCut := [⟨9,29306994,29307010⟩,
⟨128,415529992,415530229⟩]
theorem checked30306 : checkPrefixCuts (2^48) 3976200193 9 Manual.Count131072.C030306.packed 128 cuts30306 = true := by
 decide +kernel
def pointBounds30306 : List (Nat × Nat × Nat) := [(3976209408,105357161138175,105357544532069)]
theorem point_links_checked30306 : (cuts30306.take 1).map (fun c => (3976200193-1+2*2^9*c.k,105357131831181+c.lower,105357515225059+c.upper)) = pointBounds30306 := by
 decide +kernel
def cuts30307 : List PrefixCut := [⟨3,10547346,10547352⟩,
⟨125,415941169,415941399⟩,
⟨128,425284826,425285061⟩]
theorem checked30307 : checkPrefixCuts (2^48) 3976331265 9 Manual.Count131072.C030307.packed 128 cuts30307 = true := by
 decide +kernel
def pointBounds30307 : List (Nat × Nat × Nat) := [(3976334336,105357557908519,105357941302640),(3976459264,105357963302342,105358346696687)]
theorem point_links_checked30307 : (cuts30307.take 2).map (fun c => (3976331265-1+2*2^9*c.k,105357547361173+c.lower,105357930755288+c.upper)) = pointBounds30307 := by
 decide +kernel
def cuts30308 : List PrefixCut := [⟨119,389242122,389242341⟩,
⟨128,417201408,417201643⟩]
theorem checked30308 : checkPrefixCuts (2^48) 3976462337 9 Manual.Count131072.C030308.packed 128 cuts30308 = true := by
 decide +kernel
def pointBounds30308 : List (Nat × Nat × Nat) := [(3976584192,105358361888121,105358745282690)]
theorem point_links_checked30308 : (cuts30308.take 1).map (fun c => (3976462337-1+2*2^9*c.k,105357972645999+c.lower,105358356040349+c.upper)) = pointBounds30308 := by
 decide +kernel
def cuts30309 : List PrefixCut := [⟨113,375851823,375852032⟩,
⟨128,424265837,424266075⟩]
theorem checked30309 : checkPrefixCuts (2^48) 3976593409 9 Manual.Count131072.C030309.packed 128 cuts30309 = true := by
 decide +kernel
def pointBounds30309 : List (Nat × Nat × Nat) := [(3976709120,105358765699230,105359149094024)]
theorem point_links_checked30309 : (cuts30309.take 1).map (fun c => (3976593409-1+2*2^9*c.k,105358389847407+c.lower,105358773241992+c.upper)) = pointBounds30309 := by
 decide +kernel
def cuts30310 : List PrefixCut := [⟨107,349085092,349085285⟩,
⟨128,415404496,415404726⟩]
theorem checked30310 : checkPrefixCuts (2^48) 3976724481 9 Manual.Count131072.C030310.packed 128 cuts30310 = true := by
 decide +kernel
def pointBounds30310 : List (Nat × Nat × Nat) := [(3976834048,105359163198336,105359546593352)]
theorem point_links_checked30310 : (cuts30310.take 1).map (fun c => (3976724481-1+2*2^9*c.k,105358814113244+c.lower,105359197508067+c.upper)) = pointBounds30310 := by
 decide +kernel
def cuts30311 : List PrefixCut := [⟨101,333856685,333856876⟩,
⟨128,420911367,420911607⟩]
theorem checked30311 : checkPrefixCuts (2^48) 3976855553 9 Manual.Count131072.C030311.packed 128 cuts30311 = true := by
 decide +kernel
def pointBounds30311 : List (Nat × Nat × Nat) := [(3976958976,105359563374425,105359946769669)]
theorem point_links_checked30311 : (cuts30311.take 1).map (fun c => (3976855553-1+2*2^9*c.k,105359229517740+c.lower,105359612912793+c.upper)) = pointBounds30311 := by
 decide +kernel
def cuts30312 : List PrefixCut := [⟨95,310419398,310419570⟩,
⟨128,419269645,419269876⟩]
theorem checked30312 : checkPrefixCuts (2^48) 3976986625 9 Manual.Count131072.C030312.packed 128 cuts30312 = true := by
 decide +kernel
def pointBounds30312 : List (Nat × Nat × Nat) := [(3977083904,105359960848505,105360344243970)]
theorem point_links_checked30312 : (cuts30312.take 1).map (fun c => (3976986625-1+2*2^9*c.k,105359650429107+c.lower,105360033824400+c.upper)) = pointBounds30312 := by
 decide +kernel
def cuts30313 : List PrefixCut := [⟨89,292716217,292716381⟩,
⟨128,420175889,420176126⟩]
theorem checked30313 : checkPrefixCuts (2^48) 3977117697 9 Manual.Count131072.C030313.packed 128 cuts30313 = true := by
 decide +kernel
def pointBounds30313 : List (Nat × Nat × Nat) := [(3977208832,105360362414969,105360745810657)]
theorem point_links_checked30313 : (cuts30313.take 1).map (fun c => (3977117697-1+2*2^9*c.k,105360069698752+c.lower,105360453094276+c.upper)) = pointBounds30313 := by
 decide +kernel
def cuts30314 : List PrefixCut := [⟨83,271687936,271688085⟩,
⟨128,417118922,417119155⟩]
theorem checked30314 : checkPrefixCuts (2^48) 3977248769 9 Manual.Count131072.C030314.packed 128 cuts30314 = true := by
 decide +kernel
def pointBounds30314 : List (Nat × Nat × Nat) := [(3977333760,105360761562577,105361144958487)]
theorem point_links_checked30314 : (cuts30314.take 1).map (fun c => (3977248769-1+2*2^9*c.k,105360489874641+c.lower,105360873270402+c.upper)) = pointBounds30314 := by
 decide +kernel
def cuts30315 : List PrefixCut := [⟨77,250024112,250024257⟩,
⟨128,419369686,419369923⟩]
theorem checked30315 : checkPrefixCuts (2^48) 3977379841 9 Manual.Count131072.C030315.packed 128 cuts30315 = true := by
 decide +kernel
def pointBounds30315 : List (Nat × Nat × Nat) := [(3977458688,105361157017675,105361540413814)]
theorem point_links_checked30315 : (cuts30315.take 1).map (fun c => (3977379841-1+2*2^9*c.k,105360906993563+c.lower,105361290389557+c.upper)) = pointBounds30315 := by
 decide +kernel
def cuts30316 : List PrefixCut := [⟨71,232961484,232961614⟩,
⟨128,422398810,422399041⟩]
theorem checked30316 : checkPrefixCuts (2^48) 3977510913 9 Manual.Count131072.C030316.packed 128 cuts30316 = true := by
 decide +kernel
def pointBounds30316 : List (Nat × Nat × Nat) := [(3977583616,105361559324733,105361942721094)]
theorem point_links_checked30316 : (cuts30316.take 1).map (fun c => (3977510913-1+2*2^9*c.k,105361326363249+c.lower,105361709759480+c.upper)) = pointBounds30316 := by
 decide +kernel
def cuts30317 : List PrefixCut := [⟨65,209318940,209319062⟩,
⟨128,412761157,412761395⟩]
theorem checked30317 : checkPrefixCuts (2^48) 3977641985 9 Manual.Count131072.C030317.packed 128 cuts30317 = true := by
 decide +kernel
def pointBounds30317 : List (Nat × Nat × Nat) := [(3977708544,105361958080999,105362341477583)]
theorem point_links_checked30317 : (cuts30317.take 1).map (fun c => (3977641985-1+2*2^9*c.k,105361748762059+c.lower,105362132158521+c.upper)) = pointBounds30317 := by
 decide +kernel
def cuts30318 : List PrefixCut := [⟨59,193532407,193532516⟩,
⟨128,422229419,422229657⟩]
theorem checked30318 : checkPrefixCuts (2^48) 3977773057 9 Manual.Count131072.C030318.packed 128 cuts30318 = true := by
 decide +kernel
def pointBounds30318 : List (Nat × Nat × Nat) := [(3977833472,105362355055623,105362738452432)]
theorem point_links_checked30318 : (cuts30318.take 1).map (fun c => (3977773057-1+2*2^9*c.k,105362161523216+c.lower,105362544919916+c.upper)) = pointBounds30318 := by
 decide +kernel
def cuts30319 : List PrefixCut := [⟨53,172015399,172015495⟩,
⟨128,414998235,414998467⟩]
theorem checked30319 : checkPrefixCuts (2^48) 3977904129 9 Manual.Count131072.C030319.packed 128 cuts30319 = true := by
 decide +kernel
def pointBounds30319 : List (Nat × Nat × Nat) := [(3977958400,105362755768034,105363139165068)]
theorem point_links_checked30319 : (cuts30319.take 1).map (fun c => (3977904129-1+2*2^9*c.k,105362583752635+c.lower,105362967149573+c.upper)) = pointBounds30319 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000009
