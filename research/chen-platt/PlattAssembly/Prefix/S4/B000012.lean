import PlattAssemblyKernel
import PlattCertificates.Count131072.C030384
import PlattCertificates.Count131072.C030385
import PlattCertificates.Count131072.C030386
import PlattCertificates.Count131072.C030387
import PlattCertificates.Count131072.C030388
import PlattCertificates.Count131072.C030389
import PlattCertificates.Count131072.C030390
import PlattCertificates.Count131072.C030391
import PlattCertificates.Count131072.C030392
import PlattCertificates.Count131072.C030393
import PlattCertificates.Count131072.C030394
import PlattCertificates.Count131072.C030395
import PlattCertificates.Count131072.C030396
import PlattCertificates.Count131072.C030397
import PlattCertificates.Count131072.C030398
import PlattCertificates.Count131072.C030399
import PlattCertificates.Count131072.C030400
import PlattCertificates.Count131072.C030401
import PlattCertificates.Count131072.C030402
import PlattCertificates.Count131072.C030403
import PlattCertificates.Count131072.C030404
import PlattCertificates.Count131072.C030405
import PlattCertificates.Count131072.C030406
import PlattCertificates.Count131072.C030407
import PlattCertificates.Count131072.C030408
import PlattCertificates.Count131072.C030409
import PlattCertificates.Count131072.C030410
import PlattCertificates.Count131072.C030411
import PlattCertificates.Count131072.C030412
import PlattCertificates.Count131072.C030413
import PlattCertificates.Count131072.C030414
import PlattCertificates.Count131072.C030415
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000012
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts30384 : List PrefixCut := [⟨29,96733105,96733160⟩,
⟨128,419053870,419054109⟩]
theorem checked30384 : checkPrefixCuts (2^48) 3986423809 9 Manual.Count131072.C030384.packed 128 cuts30384 = true := by
 decide +kernel
def pointBounds30384 : List (Nat × Nat × Nat) := [(3986453504,105389909131484,105390292543812)]
theorem point_links_checked30384 : (cuts30384.take 1).map (fun c => (3986423809-1+2*2^9*c.k,105389812398379+c.lower,105390195810652+c.upper)) = pointBounds30384 := by
 decide +kernel
def cuts30385 : List PrefixCut := [⟨23,76395524,76395568⟩,
⟨128,420240333,420240570⟩]
theorem checked30385 : checkPrefixCuts (2^48) 3986554881 9 Manual.Count131072.C030385.packed 128 cuts30385 = true := by
 decide +kernel
def pointBounds30385 : List (Nat × Nat × Nat) := [(3986578432,105390307847773,105390691260329)]
theorem point_links_checked30385 : (cuts30385.take 1).map (fun c => (3986554881-1+2*2^9*c.k,105390231452249+c.lower,105390614864761+c.upper)) = pointBounds30385 := by
 decide +kernel
def cuts30386 : List PrefixCut := [⟨17,56977086,56977117⟩,
⟨128,421991543,421991785⟩]
theorem checked30386 : checkPrefixCuts (2^48) 3986685953 9 Manual.Count131072.C030386.packed 128 cuts30386 = true := by
 decide +kernel
def pointBounds30386 : List (Nat × Nat × Nat) := [(3986703360,105390708669668,105391092082448)]
theorem point_links_checked30386 : (cuts30386.take 1).map (fun c => (3986685953-1+2*2^9*c.k,105390651692582+c.lower,105391035105331+c.upper)) = pointBounds30386 := by
 decide +kernel
def cuts30387 : List PrefixCut := [⟨11,35159450,35159470⟩,
⟨128,412023041,412023282⟩]
theorem checked30387 : checkPrefixCuts (2^48) 3986817025 9 Manual.Count131072.C030387.packed 128 cuts30387 = true := by
 decide +kernel
def pointBounds30387 : List (Nat × Nat × Nat) := [(3986828288,105391108843575,105391492256586)]
theorem point_links_checked30387 : (cuts30387.take 1).map (fun c => (3986817025-1+2*2^9*c.k,105391073684125+c.lower,105391457097116+c.upper)) = pointBounds30387 := by
 decide +kernel
def cuts30388 : List PrefixCut := [⟨5,16802572,16802580⟩,
⟨127,414409911,414410140⟩,
⟨128,416951395,416951625⟩]
theorem checked30388 : checkPrefixCuts (2^48) 3986948097 9 Manual.Count131072.C030388.packed 128 cuts30388 = true := by
 decide +kernel
def pointBounds30388 : List (Nat × Nat × Nat) := [(3986953216,105391502509738,105391885922978),(3987078144,105391900117077,105392283530538)]
theorem point_links_checked30388 : (cuts30388.take 2).map (fun c => (3986948097-1+2*2^9*c.k,105391485707166+c.lower,105391869120398+c.upper)) = pointBounds30388 := by
 decide +kernel
def cuts30389 : List PrefixCut := [⟨121,400489259,400489485⟩,
⟨128,423291285,423291525⟩]
theorem checked30389 : checkPrefixCuts (2^48) 3987079169 9 Manual.Count131072.C030389.packed 128 cuts30389 = true := by
 decide +kernel
def pointBounds30389 : List (Nat × Nat × Nat) := [(3987203072,105392303147820,105392686561508)]
theorem point_links_checked30389 : (cuts30389.take 1).map (fun c => (3987079169-1+2*2^9*c.k,105391902658561+c.lower,105392286072023+c.upper)) = pointBounds30389 := by
 decide +kernel
def cuts30390 : List PrefixCut := [⟨115,372097833,372098045⟩,
⟨128,414594364,414594601⟩]
theorem checked30390 : checkPrefixCuts (2^48) 3987210241 9 Manual.Count131072.C030390.packed 128 cuts30390 = true := by
 decide +kernel
def pointBounds30390 : List (Nat × Nat × Nat) := [(3987328000,105392698047679,105393081461593)]
theorem point_links_checked30390 : (cuts30390.take 1).map (fun c => (3987210241-1+2*2^9*c.k,105392325949846+c.lower,105392709363548+c.upper)) = pointBounds30390 := by
 decide +kernel
def cuts30391 : List PrefixCut := [⟨109,356979407,356979609⟩,
⟨128,420510388,420510625⟩]
theorem checked30391 : checkPrefixCuts (2^48) 3987341313 9 Manual.Count131072.C030391.packed 128 cuts30391 = true := by
 decide +kernel
def pointBounds30391 : List (Nat × Nat × Nat) := [(3987452928,105393097523617,105393480937758)]
theorem point_links_checked30391 : (cuts30391.take 1).map (fun c => (3987341313-1+2*2^9*c.k,105392740544210+c.lower,105393123958149+c.upper)) = pointBounds30391 := by
 decide +kernel
def cuts30392 : List PrefixCut := [⟨103,335720668,335720852⟩,
⟨128,420214156,420214388⟩]
theorem checked30392 : checkPrefixCuts (2^48) 3987472385 9 Manual.Count131072.C030392.packed 128 cuts30392 = true := by
 decide +kernel
def pointBounds30392 : List (Nat × Nat × Nat) := [(3987577856,105393496775266,105393880189626)]
theorem point_links_checked30392 : (cuts30392.take 1).map (fun c => (3987472385-1+2*2^9*c.k,105393161054598+c.lower,105393544468774+c.upper)) = pointBounds30392 := by
 decide +kernel
def cuts30393 : List PrefixCut := [⟨97,315945642,315945820⟩,
⟨128,419423906,419424143⟩]
theorem checked30393 : checkPrefixCuts (2^48) 3987603457 9 Manual.Count131072.C030393.packed 128 cuts30393 = true := by
 decide +kernel
def pointBounds30393 : List (Nat × Nat × Nat) := [(3987702784,105393897214396,105394280628982)]
theorem point_links_checked30393 : (cuts30393.take 1).map (fun c => (3987603457-1+2*2^9*c.k,105393581268754+c.lower,105393964683162+c.upper)) = pointBounds30393 := by
 decide +kernel
def cuts30394 : List PrefixCut := [⟨91,294830768,294830937⟩,
⟨128,416304423,416304657⟩]
theorem checked30394 : checkPrefixCuts (2^48) 3987734529 9 Manual.Count131072.C030394.packed 128 cuts30394 = true := by
 decide +kernel
def pointBounds30394 : List (Nat × Nat × Nat) := [(3987827712,105394295523428,105394678938242)]
theorem point_links_checked30394 : (cuts30394.take 1).map (fun c => (3987734529-1+2*2^9*c.k,105394000692660+c.lower,105394384107305+c.upper)) = pointBounds30394 := by
 decide +kernel
def cuts30395 : List PrefixCut := [⟨85,273858463,273858617⟩,
⟨128,413538095,413538331⟩]
theorem checked30395 : checkPrefixCuts (2^48) 3987865601 9 Manual.Count131072.C030395.packed 128 cuts30395 = true := by
 decide +kernel
def pointBounds30395 : List (Nat × Nat × Nat) := [(3987952640,105394690855546,105395074270579)]
theorem point_links_checked30395 : (cuts30395.take 1).map (fun c => (3987865601-1+2*2^9*c.k,105394416997083+c.lower,105394800411962+c.upper)) = pointBounds30395 := by
 decide +kernel
def cuts30396 : List PrefixCut := [⟨79,254157880,254158029⟩,
⟨128,411265965,411266203⟩]
theorem checked30396 : checkPrefixCuts (2^48) 3987996673 9 Manual.Count131072.C030396.packed 128 cuts30396 = true := by
 decide +kernel
def pointBounds30396 : List (Nat × Nat × Nat) := [(3988077568,105395084693058,105395468108322)]
theorem point_links_checked30396 : (cuts30396.take 1).map (fun c => (3987996673-1+2*2^9*c.k,105394830535178+c.lower,105395213950293+c.upper)) = pointBounds30396 := by
 decide +kernel
def cuts30397 : List PrefixCut := [⟨73,239893077,239893215⟩,
⟨128,423462242,423462485⟩]
theorem checked30397 : checkPrefixCuts (2^48) 3988127745 9 Manual.Count131072.C030397.packed 128 cuts30397 = true := by
 decide +kernel
def pointBounds30397 : List (Nat × Nat × Nat) := [(3988202496,105395481694220,105395865109711)]
theorem point_links_checked30397 : (cuts30397.take 1).map (fun c => (3988127745-1+2*2^9*c.k,105395241801143+c.lower,105395625216496+c.upper)) = pointBounds30397 := by
 decide +kernel
def cuts30398 : List PrefixCut := [⟨67,216807278,216807400⟩,
⟨128,413144479,413144712⟩]
theorem checked30398 : checkPrefixCuts (2^48) 3988258817 9 Manual.Count131072.C030398.packed 128 cuts30398 = true := by
 decide +kernel
def pointBounds30398 : List (Nat × Nat × Nat) := [(3988327424,105395882070663,105396265486381)]
theorem point_links_checked30398 : (cuts30398.take 1).map (fun c => (3988258817-1+2*2^9*c.k,105395665263385+c.lower,105396048678981+c.upper)) = pointBounds30398 := by
 decide +kernel
def cuts30399 : List PrefixCut := [⟨61,202050550,202050660⟩,
⟨128,420399872,420400104⟩]
theorem checked30399 : checkPrefixCuts (2^48) 3988389889 9 Manual.Count131072.C030399.packed 128 cuts30399 = true := by
 decide +kernel
def pointBounds30399 : List (Nat × Nat × Nat) := [(3988452352,105396280458414,105396663874353)]
theorem point_links_checked30399 : (cuts30399.take 1).map (fun c => (3988389889-1+2*2^9*c.k,105396078407864+c.lower,105396461823693+c.upper)) = pointBounds30399 := by
 decide +kernel
def cuts30400 : List PrefixCut := [⟨55,176426853,176426956⟩,
⟨128,411564724,411564966⟩]
theorem checked30400 : checkPrefixCuts (2^48) 3988520961 9 Manual.Count131072.C030400.packed 128 cuts30400 = true := by
 decide +kernel
def pointBounds30400 : List (Nat × Nat × Nat) := [(3988577280,105396675234589,105397058650753)]
theorem point_links_checked30400 : (cuts30400.take 1).map (fun c => (3988520961-1+2*2^9*c.k,105396498807736+c.lower,105396882223797+c.upper)) = pointBounds30400 := by
 decide +kernel
def cuts30401 : List PrefixCut := [⟨49,162519221,162519313⟩,
⟨128,419737109,419737346⟩]
theorem checked30401 : checkPrefixCuts (2^48) 3988652033 9 Manual.Count131072.C030401.packed 128 cuts30401 = true := by
 decide +kernel
def pointBounds30401 : List (Nat × Nat × Nat) := [(3988702208,105397072891681,105397456308076)]
theorem point_links_checked30401 : (cuts30401.take 1).map (fun c => (3988652033-1+2*2^9*c.k,105396910372460+c.lower,105397293788763+c.upper)) = pointBounds30401 := by
 decide +kernel
def cuts30402 : List PrefixCut := [⟨43,144801880,144801958⟩,
⟨128,423886658,423886891⟩]
theorem checked30402 : checkPrefixCuts (2^48) 3988783105 9 Manual.Count131072.C030402.packed 128 cuts30402 = true := by
 decide +kernel
def pointBounds30402 : List (Nat × Nat × Nat) := [(3988827136,105397474911449,105397858328067)]
theorem point_links_checked30402 : (cuts30402.take 1).map (fun c => (3988783105-1+2*2^9*c.k,105397330109569+c.lower,105397713526109+c.upper)) = pointBounds30402 := by
 decide +kernel
def cuts30403 : List PrefixCut := [⟨37,122287338,122287406⟩,
⟨128,420415124,420415362⟩]
theorem checked30403 : checkPrefixCuts (2^48) 3988914177 9 Manual.Count131072.C030403.packed 128 cuts30403 = true := by
 decide +kernel
def pointBounds30403 : List (Nat × Nat × Nat) := [(3988952064,105397876283565,105398259700406)]
theorem point_links_checked30403 : (cuts30403.take 1).map (fun c => (3988914177-1+2*2^9*c.k,105397753996227+c.lower,105398137413000+c.upper)) = pointBounds30403 := by
 decide +kernel
def cuts30404 : List PrefixCut := [⟨31,100056474,100056530⟩,
⟨128,418213935,418214168⟩]
theorem checked30404 : checkPrefixCuts (2^48) 3989045249 9 Manual.Count131072.C030404.packed 128 cuts30404 = true := by
 decide +kernel
def pointBounds30404 : List (Nat × Nat × Nat) := [(3989076992,105398274467825,105398657884892)]
theorem point_links_checked30404 : (cuts30404.take 1).map (fun c => (3989045249-1+2*2^9*c.k,105398174411351+c.lower,105398557828362+c.upper)) = pointBounds30404 := by
 decide +kernel
def cuts30405 : List PrefixCut := [⟨25,80719987,80720032⟩,
⟨128,420034752,420034987⟩]
theorem checked30405 : checkPrefixCuts (2^48) 3989176321 9 Manual.Count131072.C030405.packed 128 cuts30405 = true := by
 decide +kernel
def pointBounds30405 : List (Nat × Nat × Nat) := [(3989201920,105398673345273,105399056762562)]
theorem point_links_checked30405 : (cuts30405.take 1).map (fun c => (3989176321-1+2*2^9*c.k,105398592625286+c.lower,105398976042530+c.upper)) = pointBounds30405 := by
 decide +kernel
def cuts30406 : List PrefixCut := [⟨19,62160860,62160896⟩,
⟨128,417339820,417340050⟩]
theorem checked30406 : checkPrefixCuts (2^48) 3989307393 9 Manual.Count131072.C030406.packed 128 cuts30406 = true := by
 decide +kernel
def pointBounds30406 : List (Nat × Nat × Nat) := [(3989326848,105399074820898,105399458238413)]
theorem point_links_checked30406 : (cuts30406.take 1).map (fun c => (3989307393-1+2*2^9*c.k,105399012660038+c.lower,105399396077517+c.upper)) = pointBounds30406 := by
 decide +kernel
def cuts30407 : List PrefixCut := [⟨13,42967933,42967958⟩,
⟨128,419513245,419513479⟩]
theorem checked30407 : checkPrefixCuts (2^48) 3989438465 9 Manual.Count131072.C030407.packed 128 cuts30407 = true := by
 decide +kernel
def pointBounds30407 : List (Nat × Nat × Nat) := [(3989451776,105399472967791,105399856385525)]
theorem point_links_checked30407 : (cuts30407.take 1).map (fun c => (3989438465-1+2*2^9*c.k,105399429999858+c.lower,105399813417567+c.upper)) = pointBounds30407 := by
 decide +kernel
def cuts30408 : List PrefixCut := [⟨7,22294632,22294645⟩,
⟨128,422109881,422110120⟩]
theorem checked30408 : checkPrefixCuts (2^48) 3989569537 9 Manual.Count131072.C030408.packed 128 cuts30408 = true := by
 decide +kernel
def pointBounds30408 : List (Nat × Nat × Nat) := [(3989576704,105399871807735,105400255225691)]
theorem point_links_checked30408 : (cuts30408.take 1).map (fun c => (3989569537-1+2*2^9*c.k,105399849513103+c.lower,105400232931046+c.upper)) = pointBounds30408 := by
 decide +kernel
def cuts30409 : List PrefixCut := [⟨1,2680914,2680916⟩,
⟨123,401425268,401425501⟩,
⟨128,416310918,416311161⟩]
theorem checked30409 : checkPrefixCuts (2^48) 3989700609 9 Manual.Count131072.C030409.packed 128 cuts30409 = true := by
 decide +kernel
def pointBounds30409 : List (Nat × Nat × Nat) := [(3989701632,105400274303898,105400657722082),(3989826560,105400673048252,105401056466667)]
theorem point_links_checked30409 : (cuts30409.take 2).map (fun c => (3989700609-1+2*2^9*c.k,105400271622984+c.lower,105400655041166+c.upper)) = pointBounds30409 := by
 decide +kernel
def cuts30410 : List PrefixCut := [⟨117,377638178,377638385⟩,
⟨128,413757651,413757878⟩]
theorem checked30410 : checkPrefixCuts (2^48) 3989831681 9 Manual.Count131072.C030410.packed 128 cuts30410 = true := by
 decide +kernel
def pointBounds30410 : List (Nat × Nat × Nat) := [(3989951488,105401065572080,105401448990712)]
theorem point_links_checked30410 : (cuts30410.take 1).map (fun c => (3989831681-1+2*2^9*c.k,105400687933902+c.lower,105401071352327+c.upper)) = pointBounds30410 := by
 decide +kernel
def cuts30411 : List PrefixCut := [⟨111,366409390,366409600⟩,
⟨128,421433386,421433625⟩]
theorem checked30411 : checkPrefixCuts (2^48) 3989962753 9 Manual.Count131072.C030411.packed 128 cuts30411 = true := by
 decide +kernel
def pointBounds30411 : List (Nat × Nat × Nat) := [(3990076416,105401468100943,105401851519805)]
theorem point_links_checked30411 : (cuts30411.take 1).map (fun c => (3989962753-1+2*2^9*c.k,105401101691553+c.lower,105401485110205+c.upper)) = pointBounds30411 := by
 decide +kernel
def cuts30412 : List PrefixCut := [⟨105,335641129,335641313⟩,
⟨128,413941991,413942217⟩]
theorem checked30412 : checkPrefixCuts (2^48) 3990093825 9 Manual.Count131072.C030412.packed 128 cuts30412 = true := by
 decide +kernel
def pointBounds30412 : List (Nat × Nat × Nat) := [(3990201344,105401858766068,105402242185143)]
theorem point_links_checked30412 : (cuts30412.take 1).map (fun c => (3990093825-1+2*2^9*c.k,105401523124939+c.lower,105401906543830+c.upper)) = pointBounds30412 := by
 decide +kernel
def cuts30413 : List PrefixCut := [⟨99,320887389,320887571⟩,
⟨128,417173202,417173439⟩]
theorem checked30413 : checkPrefixCuts (2^48) 3990224897 9 Manual.Count131072.C030413.packed 128 cuts30413 = true := by
 decide +kernel
def pointBounds30413 : List (Nat × Nat × Nat) := [(3990326272,105402257954319,105402641373618)]
theorem point_links_checked30413 : (cuts30413.take 1).map (fun c => (3990224897-1+2*2^9*c.k,105401937066930+c.lower,105402320486047+c.upper)) = pointBounds30413 := by
 decide +kernel
def cuts30414 : List PrefixCut := [⟨93,305358809,305358980⟩,
⟨128,417441785,417442018⟩]
theorem checked30414 : checkPrefixCuts (2^48) 3990355969 9 Manual.Count131072.C030414.packed 128 cuts30414 = true := by
 decide +kernel
def pointBounds30414 : List (Nat × Nat × Nat) := [(3990451200,105402659598941,105403043018466)]
theorem point_links_checked30414 : (cuts30414.take 1).map (fun c => (3990355969-1+2*2^9*c.k,105402354240132+c.lower,105402737659486+c.upper)) = pointBounds30414 := by
 decide +kernel
def cuts30415 : List PrefixCut := [⟨87,279885574,279885729⟩,
⟨128,412490492,412490721⟩]
theorem checked30415 : checkPrefixCuts (2^48) 3990487041 9 Manual.Count131072.C030415.packed 128 cuts30415 = true := by
 decide +kernel
def pointBounds30415 : List (Nat × Nat × Nat) := [(3990576128,105403051567491,105403434987233)]
theorem point_links_checked30415 : (cuts30415.take 1).map (fun c => (3990487041-1+2*2^9*c.k,105402771681917+c.lower,105403155101504+c.upper)) = pointBounds30415 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000012
