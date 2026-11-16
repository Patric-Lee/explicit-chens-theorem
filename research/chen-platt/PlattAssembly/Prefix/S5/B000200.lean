import PlattAssemblyKernel
import PlattCertificates.Count131072.C046400
import PlattCertificates.Count131072.C046401
import PlattCertificates.Count131072.C046402
import PlattCertificates.Count131072.C046403
import PlattCertificates.Count131072.C046404
import PlattCertificates.Count131072.C046405
import PlattCertificates.Count131072.C046406
import PlattCertificates.Count131072.C046407
import PlattCertificates.Count131072.C046408
import PlattCertificates.Count131072.C046409
import PlattCertificates.Count131072.C046410
import PlattCertificates.Count131072.C046411
import PlattCertificates.Count131072.C046412
import PlattCertificates.Count131072.C046413
import PlattCertificates.Count131072.C046414
import PlattCertificates.Count131072.C046415
import PlattCertificates.Count131072.C046416
import PlattCertificates.Count131072.C046417
import PlattCertificates.Count131072.C046418
import PlattCertificates.Count131072.C046419
import PlattCertificates.Count131072.C046420
import PlattCertificates.Count131072.C046421
import PlattCertificates.Count131072.C046422
import PlattCertificates.Count131072.C046423
import PlattCertificates.Count131072.C046424
import PlattCertificates.Count131072.C046425
import PlattCertificates.Count131072.C046426
import PlattCertificates.Count131072.C046427
import PlattCertificates.Count131072.C046428
import PlattCertificates.Count131072.C046429
import PlattCertificates.Count131072.C046430
import PlattCertificates.Count131072.C046431
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000200
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts46400 : List PrefixCut := [⟨58,243607204,243607341⟩,
⟨64,268906560,268906712⟩]
theorem checked46400 : checkPrefixCuts (2^48) 6085672961 10 Manual.Count131072.C046400.packed 64 cuts46400 = true := by
 decide +kernel
def pointBounds46400 : List (Nat × Nat × Nat) := [(6085791744,110725632906980,110726019496623)]
theorem point_links_checked46400 : (cuts46400.take 1).map (fun c => (6085672961-1+2*2^10*c.k,110725389299776+c.lower,110725775889282+c.upper)) = pointBounds46400 := by
 decide +kernel
def cuts46401 : List PrefixCut := [⟨64,266958256,266958406⟩]
theorem checked46401 : checkPrefixCuts (2^48) 6085804033 10 Manual.Count131072.C046401.packed 64 cuts46401 = true := by
 decide +kernel
def cuts46402 : List PrefixCut := [⟨23,96939754,96939813⟩,
⟨64,268062506,268062658⟩]
theorem checked46402 : checkPrefixCuts (2^48) 6085935105 10 Manual.Count131072.C046402.packed 64 cuts46402 = true := by
 decide +kernel
def pointBounds46402 : List (Nat × Nat × Nat) := [(6085982208,110726022104346,110726408694213)]
theorem point_links_checked46402 : (cuts46402.take 1).map (fun c => (6085935105-1+2*2^10*c.k,110725925164592+c.lower,110726311754400+c.upper)) = pointBounds46402 := by
 decide +kernel
def cuts46403 : List PrefixCut := [⟨52,221716096,221716230⟩,
⟨64,270507910,270508070⟩]
theorem checked46403 : checkPrefixCuts (2^48) 6086066177 10 Manual.Count131072.C046403.packed 64 cuts46403 = true := by
 decide +kernel
def pointBounds46403 : List (Nat × Nat × Nat) := [(6086172672,110726414943194,110726801533288)]
theorem point_links_checked46403 : (cuts46403.take 1).map (fun c => (6086066177-1+2*2^10*c.k,110726193227098+c.lower,110726579817058+c.upper)) = pointBounds46403 := by
 decide +kernel
def cuts46404 : List PrefixCut := [⟨64,267310966,267311118⟩]
theorem checked46404 : checkPrefixCuts (2^48) 6086197249 10 Manual.Count131072.C046404.packed 64 cuts46404 = true := by
 decide +kernel
def cuts46405 : List PrefixCut := [⟨17,70989060,70989100⟩,
⟨64,267258992,267259146⟩]
theorem checked46405 : checkPrefixCuts (2^48) 6086328321 10 Manual.Count131072.C046405.packed 64 cuts46405 = true := by
 decide +kernel
def pointBounds46405 : List (Nat × Nat × Nat) := [(6086363136,110726802035034,110727188625346)]
theorem point_links_checked46405 : (cuts46405.take 1).map (fun c => (6086328321-1+2*2^10*c.k,110726731045974+c.lower,110727117636246+c.upper)) = pointBounds46405 := by
 decide +kernel
def cuts46406 : List PrefixCut := [⟨46,191688531,191688644⟩,
⟨64,269195526,269195688⟩]
theorem checked46406 : checkPrefixCuts (2^48) 6086459393 10 Manual.Count131072.C046406.packed 64 cuts46406 = true := by
 decide +kernel
def pointBounds46406 : List (Nat × Nat × Nat) := [(6086553600,110727189993497,110727576584036)]
theorem point_links_checked46406 : (cuts46406.take 1).map (fun c => (6086459393-1+2*2^10*c.k,110726998304966+c.lower,110727384895392+c.upper)) = pointBounds46406 := by
 decide +kernel
def cuts46407 : List PrefixCut := [⟨64,265258947,265259095⟩]
theorem checked46407 : checkPrefixCuts (2^48) 6086590465 10 Manual.Count131072.C046407.packed 64 cuts46407 = true := by
 decide +kernel
def cuts46408 : List PrefixCut := [⟨11,47168885,47168911⟩,
⟨64,270571250,270571404⟩]
theorem checked46408 : checkPrefixCuts (2^48) 6086721537 10 Manual.Count131072.C046408.packed 64 cuts46408 = true := by
 decide +kernel
def pointBounds46408 : List (Nat × Nat × Nat) := [(6086744064,110727579928324,110727966519086)]
theorem point_links_checked46408 : (cuts46408.take 1).map (fun c => (6086721537-1+2*2^10*c.k,110727532759439+c.lower,110727919350175+c.upper)) = pointBounds46408 := by
 decide +kernel
def cuts46409 : List PrefixCut := [⟨40,168924883,168924984⟩,
⟨64,270750387,270750546⟩]
theorem checked46409 : checkPrefixCuts (2^48) 6086852609 10 Manual.Count131072.C046409.packed 64 cuts46409 = true := by
 decide +kernel
def pointBounds46409 : List (Nat × Nat × Nat) := [(6086934528,110727972255572,110728358846563)]
theorem point_links_checked46409 : (cuts46409.take 1).map (fun c => (6086852609-1+2*2^10*c.k,110727803330689+c.lower,110728189921579+c.upper)) = pointBounds46409 := by
 decide +kernel
def cuts46410 : List PrefixCut := [⟨64,270467094,270467251⟩]
theorem checked46410 : checkPrefixCuts (2^48) 6086983681 10 Manual.Count131072.C046410.packed 64 cuts46410 = true := by
 decide +kernel
def cuts46411 : List PrefixCut := [⟨5,20346068,20346080⟩,
⟨64,267964302,267964456⟩]
theorem checked46411 : checkPrefixCuts (2^48) 6087114753 10 Manual.Count131072.C046411.packed 64 cuts46411 = true := by
 decide +kernel
def pointBounds46411 : List (Nat × Nat × Nat) := [(6087124992,110728364894238,110728751485456)]
theorem point_links_checked46411 : (cuts46411.take 1).map (fun c => (6087114753-1+2*2^10*c.k,110728344548170+c.lower,110728731139376+c.upper)) = pointBounds46411 := by
 decide +kernel
def cuts46412 : List PrefixCut := [⟨34,142511202,142511281⟩,
⟨64,271102818,271102970⟩]
theorem checked46412 : checkPrefixCuts (2^48) 6087245825 10 Manual.Count131072.C046412.packed 64 cuts46412 = true := by
 decide +kernel
def pointBounds46412 : List (Nat × Nat × Nat) := [(6087315456,110728755023674,110729141615113)]
theorem point_links_checked46412 : (cuts46412.take 1).map (fun c => (6087245825-1+2*2^10*c.k,110728612512472+c.lower,110728999103832+c.upper)) = pointBounds46412 := by
 decide +kernel
def cuts46413 : List PrefixCut := [⟨63,266750614,266750764⟩,
⟨64,270680854,270681007⟩]
theorem checked46413 : checkPrefixCuts (2^48) 6087376897 10 Manual.Count131072.C046413.packed 64 cuts46413 = true := by
 decide +kernel
def pointBounds46413 : List (Nat × Nat × Nat) := [(6087505920,110729150365904,110729536957566)]
theorem point_links_checked46413 : (cuts46413.take 1).map (fun c => (6087376897-1+2*2^10*c.k,110728883615290+c.lower,110729270206802+c.upper)) = pointBounds46413 := by
 decide +kernel
def cuts46414 : List PrefixCut := [⟨64,268779277,268779433⟩]
theorem checked46414 : checkPrefixCuts (2^48) 6087507969 10 Manual.Count131072.C046414.packed 64 cuts46414 = true := by
 decide +kernel
def cuts46415 : List PrefixCut := [⟨28,118227761,118227829⟩,
⟨64,270253065,270253223⟩]
theorem checked46415 : checkPrefixCuts (2^48) 6087639041 10 Manual.Count131072.C046415.packed 64 cuts46415 = true := by
 decide +kernel
def pointBounds46415 : List (Nat × Nat × Nat) := [(6087696384,110729541303182,110729927895071)]
theorem point_links_checked46415 : (cuts46415.take 1).map (fun c => (6087639041-1+2*2^10*c.k,110729423075421+c.lower,110729809667242+c.upper)) = pointBounds46415 := by
 decide +kernel
def cuts46416 : List PrefixCut := [⟨57,239547042,239547187⟩,
⟨64,268998854,268999015⟩]
theorem checked46416 : checkPrefixCuts (2^48) 6087770113 10 Manual.Count131072.C046416.packed 64 cuts46416 = true := by
 decide +kernel
def pointBounds46416 : List (Nat × Nat × Nat) := [(6087886848,110729932875528,110730319467652)]
theorem point_links_checked46416 : (cuts46416.take 1).map (fun c => (6087770113-1+2*2^10*c.k,110729693328486+c.lower,110730079920465+c.upper)) = pointBounds46416 := by
 decide +kernel
def cuts46417 : List PrefixCut := [⟨64,267698506,267698656⟩]
theorem checked46417 : checkPrefixCuts (2^48) 6087901185 10 Manual.Count131072.C046417.packed 64 cuts46417 = true := by
 decide +kernel
def cuts46418 : List PrefixCut := [⟨22,93901177,93901231⟩,
⟨64,266490697,266490854⟩]
theorem checked46418 : checkPrefixCuts (2^48) 6088032257 10 Manual.Count131072.C046418.packed 64 cuts46418 = true := by
 decide +kernel
def pointBounds46418 : List (Nat × Nat × Nat) := [(6088077312,110730323927023,110730710519367)]
theorem point_links_checked46418 : (cuts46418.take 1).map (fun c => (6088032257-1+2*2^10*c.k,110730230025846+c.lower,110730616618136+c.upper)) = pointBounds46418 := by
 decide +kernel
def cuts46419 : List PrefixCut := [⟨51,213410323,213410444⟩,
⟨64,268149295,268149451⟩]
theorem checked46419 : checkPrefixCuts (2^48) 6088163329 10 Manual.Count131072.C046419.packed 64 cuts46419 = true := by
 decide +kernel
def pointBounds46419 : List (Nat × Nat × Nat) := [(6088267776,110730709926866,110731096519434)]
theorem point_links_checked46419 : (cuts46419.take 1).map (fun c => (6088163329-1+2*2^10*c.k,110730496516543+c.lower,110730883108990+c.upper)) = pointBounds46419 := by
 decide +kernel
def cuts46420 : List PrefixCut := [⟨64,268929506,268929660⟩]
theorem checked46420 : checkPrefixCuts (2^48) 6088294401 10 Manual.Count131072.C046420.packed 64 cuts46420 = true := by
 decide +kernel
def cuts46421 : List PrefixCut := [⟨16,67312369,67312408⟩,
⟨64,269524685,269524839⟩]
theorem checked46421 : checkPrefixCuts (2^48) 6088425473 10 Manual.Count131072.C046421.packed 64 cuts46421 = true := by
 decide +kernel
def pointBounds46421 : List (Nat × Nat × Nat) := [(6088458240,110731100907713,110731487500509)]
theorem point_links_checked46421 : (cuts46421.take 1).map (fun c => (6088425473-1+2*2^10*c.k,110731033595344+c.lower,110731420188101+c.upper)) = pointBounds46421 := by
 decide +kernel
def cuts46422 : List PrefixCut := [⟨45,188987419,188987527⟩,
⟨64,269472638,269472793⟩]
theorem checked46422 : checkPrefixCuts (2^48) 6088556545 10 Manual.Count131072.C046422.packed 64 cuts46422 = true := by
 decide +kernel
def pointBounds46422 : List (Nat × Nat × Nat) := [(6088648704,110731492107448,110731878700467)]
theorem point_links_checked46422 : (cuts46422.take 1).map (fun c => (6088556545-1+2*2^10*c.k,110731303120029+c.lower,110731689712940+c.upper)) = pointBounds46422 := by
 decide +kernel
def cuts46423 : List PrefixCut := [⟨64,268218668,268218827⟩]
theorem checked46423 : checkPrefixCuts (2^48) 6088687617 10 Manual.Count131072.C046423.packed 64 cuts46423 = true := by
 decide +kernel
def cuts46424 : List PrefixCut := [⟨10,41512819,41512844⟩,
⟨64,269507291,269507444⟩]
theorem checked46424 : checkPrefixCuts (2^48) 6088818689 10 Manual.Count131072.C046424.packed 64 cuts46424 = true := by
 decide +kernel
def pointBounds46424 : List (Nat × Nat × Nat) := [(6088839168,110731882324154,110732268917404)]
theorem point_links_checked46424 : (cuts46424.take 1).map (fun c => (6088818689-1+2*2^10*c.k,110731840811335+c.lower,110732227404560+c.upper)) = pointBounds46424 := by
 decide +kernel
def cuts46425 : List PrefixCut := [⟨39,168127094,168127192⟩,
⟨64,272182640,272182797⟩]
theorem checked46425 : checkPrefixCuts (2^48) 6088949761 10 Manual.Count131072.C046425.packed 64 cuts46425 = true := by
 decide +kernel
def pointBounds46425 : List (Nat × Nat × Nat) := [(6089029632,110732278445720,110732665039196)]
theorem point_links_checked46425 : (cuts46425.take 1).map (fun c => (6088949761-1+2*2^10*c.k,110732110318626+c.lower,110732496912004+c.upper)) = pointBounds46425 := by
 decide +kernel
def cuts46426 : List PrefixCut := [⟨64,272130536,272130690⟩]
theorem checked46426 : checkPrefixCuts (2^48) 6089080833 10 Manual.Count131072.C046426.packed 64 cuts46426 = true := by
 decide +kernel
def cuts46427 : List PrefixCut := [⟨4,16040127,16040135⟩,
⟨64,269351185,269351346⟩]
theorem checked46427 : checkPrefixCuts (2^48) 6089211905 10 Manual.Count131072.C046427.packed 64 cuts46427 = true := by
 decide +kernel
def pointBounds46427 : List (Nat × Nat × Nat) := [(6089220096,110732670671929,110733057265626)]
theorem point_links_checked46427 : (cuts46427.take 1).map (fun c => (6089211905-1+2*2^10*c.k,110732654631802+c.lower,110733041225491+c.upper)) = pointBounds46427 := by
 decide +kernel
def cuts46428 : List PrefixCut := [⟨33,137238831,137238908⟩,
⟨64,264445701,264445852⟩]
theorem checked46428 : checkPrefixCuts (2^48) 6089342977 10 Manual.Count131072.C046428.packed 64 cuts46428 = true := by
 decide +kernel
def pointBounds46428 : List (Nat × Nat × Nat) := [(6089410560,110733061221818,110733447815745)]
theorem point_links_checked46428 : (cuts46428.take 1).map (fun c => (6089342977-1+2*2^10*c.k,110732923982987+c.lower,110733310576837+c.upper)) = pointBounds46428 := by
 decide +kernel
def cuts46429 : List PrefixCut := [⟨62,259956492,259956640⟩,
⟨64,269200933,269201087⟩]
theorem checked46429 : checkPrefixCuts (2^48) 6089474049 10 Manual.Count131072.C046429.packed 64 cuts46429 = true := by
 decide +kernel
def pointBounds46429 : List (Nat × Nat × Nat) := [(6089601024,110733448385180,110733834979329)]
theorem point_links_checked46429 : (cuts46429.take 1).map (fun c => (6089474049-1+2*2^10*c.k,110733188428688+c.lower,110733575022689+c.upper)) = pointBounds46429 := by
 decide +kernel
def cuts46430 : List PrefixCut := [⟨64,269148909,269149065⟩]
theorem checked46430 : checkPrefixCuts (2^48) 6089605121 10 Manual.Count131072.C046430.packed 64 cuts46430 = true := by
 decide +kernel
def cuts46431 : List PrefixCut := [⟨27,114165840,114165903⟩,
⟨64,267155664,267155813⟩]
theorem checked46431 : checkPrefixCuts (2^48) 6089736193 10 Manual.Count131072.C046431.packed 64 cuts46431 = true := by
 decide +kernel
def pointBounds46431 : List (Nat × Nat × Nat) := [(6089791488,110733840944370,110734227538744)]
theorem point_links_checked46431 : (cuts46431.take 1).map (fun c => (6089736193-1+2*2^10*c.k,110733726778530+c.lower,110734113372841+c.upper)) = pointBounds46431 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000200
