import PlattAssemblyKernel
import PlattCertificates.Count131072.C061408
import PlattCertificates.Count131072.C061409
import PlattCertificates.Count131072.C061410
import PlattCertificates.Count131072.C061411
import PlattCertificates.Count131072.C061412
import PlattCertificates.Count131072.C061413
import PlattCertificates.Count131072.C061414
import PlattCertificates.Count131072.C061415
import PlattCertificates.Count131072.C061416
import PlattCertificates.Count131072.C061417
import PlattCertificates.Count131072.C061418
import PlattCertificates.Count131072.C061419
import PlattCertificates.Count131072.C061420
import PlattCertificates.Count131072.C061421
import PlattCertificates.Count131072.C061422
import PlattCertificates.Count131072.C061423
import PlattCertificates.Count131072.C061424
import PlattCertificates.Count131072.C061425
import PlattCertificates.Count131072.C061426
import PlattCertificates.Count131072.C061427
import PlattCertificates.Count131072.C061428
import PlattCertificates.Count131072.C061429
import PlattCertificates.Count131072.C061430
import PlattCertificates.Count131072.C061431
import PlattCertificates.Count131072.C061432
import PlattCertificates.Count131072.C061433
import PlattCertificates.Count131072.C061434
import PlattCertificates.Count131072.C061435
import PlattCertificates.Count131072.C061436
import PlattCertificates.Count131072.C061437
import PlattCertificates.Count131072.C061438
import PlattCertificates.Count131072.C061439
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000044
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts61408 : List PrefixCut := [⟨64,199269183,199269295⟩]
theorem checked61408 : checkPrefixCuts (2^48) 8052801537 10 Manual.Count131072.C061408.packed 64 cuts61408 = true := by
 decide +kernel
def cuts61409 : List PrefixCut := [⟨16,49318715,49318743⟩,
⟨64,202271899,202272012⟩]
theorem checked61409 : checkPrefixCuts (2^48) 8052932609 10 Manual.Count131072.C061409.packed 64 cuts61409 = true := by
 decide +kernel
def pointBounds61409 : List (Nat × Nat × Nat) := [(8052965376,114203319597032,114203708168131)]
theorem point_links_checked61409 : (cuts61409.take 1).map (fun c => (8052932609-1+2*2^10*c.k,114203270278317+c.lower,114203658849388+c.upper)) = pointBounds61409 := by
 decide +kernel
def cuts61410 : List PrefixCut := [⟨64,199856923,199857039⟩]
theorem checked61410 : checkPrefixCuts (2^48) 8053063681 10 Manual.Count131072.C061410.packed 64 cuts61410 = true := by
 decide +kernel
def cuts61411 : List PrefixCut := [⟨11,35581041,35581057⟩,
⟨64,201636193,201636297⟩]
theorem checked61411 : checkPrefixCuts (2^48) 8053194753 10 Manual.Count131072.C061411.packed 64 cuts61411 = true := by
 decide +kernel
def pointBounds61411 : List (Nat × Nat × Nat) := [(8053217280,114203707988180,114204096559496)]
theorem point_links_checked61411 : (cuts61411.take 1).map (fun c => (8053194753-1+2*2^10*c.k,114203672407139+c.lower,114204060978439+c.upper)) = pointBounds61411 := by
 decide +kernel
def cuts61412 : List PrefixCut := [⟨64,201388230,201388347⟩]
theorem checked61412 : checkPrefixCuts (2^48) 8053325825 10 Manual.Count131072.C061412.packed 64 cuts61412 = true := by
 decide +kernel
def cuts61413 : List PrefixCut := [⟨6,18384115,18384126⟩,
⟨64,198623871,198623982⟩]
theorem checked61413 : checkPrefixCuts (2^48) 8053456897 10 Manual.Count131072.C061413.packed 64 cuts61413 = true := by
 decide +kernel
def pointBounds61413 : List (Nat × Nat × Nat) := [(8053469184,114204093815677,114204482387209)]
theorem point_links_checked61413 : (cuts61413.take 1).map (fun c => (8053456897-1+2*2^10*c.k,114204075431562+c.lower,114204464003083+c.upper)) = pointBounds61413 := by
 decide +kernel
def cuts61414 : List PrefixCut := [⟨64,202045746,202045866⟩]
theorem checked61414 : checkPrefixCuts (2^48) 8053587969 10 Manual.Count131072.C061414.packed 64 cuts61414 = true := by
 decide +kernel
def cuts61415 : List PrefixCut := [⟨1,3355169,3355171⟩,
⟨64,204349102,204349218⟩]
theorem checked61415 : checkPrefixCuts (2^48) 8053719041 10 Manual.Count131072.C061415.packed 64 cuts61415 = true := by
 decide +kernel
def pointBounds61415 : List (Nat × Nat × Nat) := [(8053721088,114204479456348,114204868028102)]
theorem point_links_checked61415 : (cuts61415.take 1).map (fun c => (8053719041-1+2*2^10*c.k,114204476101179+c.lower,114204864672931+c.upper)) = pointBounds61415 := by
 decide +kernel
def cuts61416 : List PrefixCut := [⟨60,186661790,186661894⟩,
⟨64,199592758,199592869⟩]
theorem checked61416 : checkPrefixCuts (2^48) 8053850113 10 Manual.Count131072.C061416.packed 64 cuts61416 = true := by
 decide +kernel
def pointBounds61416 : List (Nat × Nat × Nat) := [(8053972992,114204867112071,114205255684043)]
theorem point_links_checked61416 : (cuts61416.take 1).map (fun c => (8053850113-1+2*2^10*c.k,114204680450281+c.lower,114205069022149+c.upper)) = pointBounds61416 := by
 decide +kernel
def cuts61417 : List PrefixCut := [⟨64,198366311,198366427⟩]
theorem checked61417 : checkPrefixCuts (2^48) 8053981185 10 Manual.Count131072.C061417.packed 64 cuts61417 = true := by
 decide +kernel
def cuts61418 : List PrefixCut := [⟨55,172222409,172222508⟩,
⟨64,201263736,201263849⟩]
theorem checked61418 : checkPrefixCuts (2^48) 8054112257 10 Manual.Count131072.C061418.packed 64 cuts61418 = true := by
 decide +kernel
def pointBounds61418 : List (Nat × Nat × Nat) := [(8054224896,114205250631759,114205639203953)]
theorem point_links_checked61418 : (cuts61418.take 1).map (fun c => (8054112257-1+2*2^10*c.k,114205078409350+c.lower,114205466981445+c.upper)) = pointBounds61418 := by
 decide +kernel
def cuts61419 : List PrefixCut := [⟨64,201435201,201435317⟩]
theorem checked61419 : checkPrefixCuts (2^48) 8054243329 10 Manual.Count131072.C061419.packed 64 cuts61419 = true := by
 decide +kernel
def cuts61420 : List PrefixCut := [⟨50,158273209,158273299⟩,
⟨64,201222244,201222361⟩]
theorem checked61420 : checkPrefixCuts (2^48) 8054374401 10 Manual.Count131072.C061420.packed 64 cuts61420 = true := by
 decide +kernel
def pointBounds61420 : List (Nat × Nat × Nat) := [(8054476800,114205639381496,114206027953910)]
theorem point_links_checked61420 : (cuts61420.take 1).map (fun c => (8054374401-1+2*2^10*c.k,114205481108287+c.lower,114205869680611+c.upper)) = pointBounds61420 := by
 decide +kernel
def cuts61421 : List PrefixCut := [⟨64,199401770,199401889⟩]
theorem checked61421 : checkPrefixCuts (2^48) 8054505473 10 Manual.Count131072.C061421.packed 64 cuts61421 = true := by
 decide +kernel
def cuts61422 : List PrefixCut := [⟨45,141424434,141424514⟩,
⟨64,201635037,201635151⟩]
theorem checked61422 : checkPrefixCuts (2^48) 8054636545 10 Manual.Count131072.C061422.packed 64 cuts61422 = true := by
 decide +kernel
def pointBounds61422 : List (Nat × Nat × Nat) := [(8054728704,114206023156735,114206411729375)]
theorem point_links_checked61422 : (cuts61422.take 1).map (fun c => (8054636545-1+2*2^10*c.k,114205881732301+c.lower,114206270304861+c.upper)) = pointBounds61422 := by
 decide +kernel
def cuts61423 : List PrefixCut := [⟨64,200967803,200967916⟩]
theorem checked61423 : checkPrefixCuts (2^48) 8054767617 10 Manual.Count131072.C061423.packed 64 cuts61423 = true := by
 decide +kernel
def cuts61424 : List PrefixCut := [⟨40,128455560,128455632⟩,
⟨64,202502109,202502221⟩]
theorem checked61424 : checkPrefixCuts (2^48) 8054898689 10 Manual.Count131072.C061424.packed 64 cuts61424 = true := by
 decide +kernel
def pointBounds61424 : List (Nat × Nat × Nat) := [(8054980608,114206412790701,114206801363560)]
theorem point_links_checked61424 : (cuts61424.take 1).map (fun c => (8054898689-1+2*2^10*c.k,114206284335141+c.lower,114206672907928+c.upper)) = pointBounds61424 := by
 decide +kernel
def cuts61425 : List PrefixCut := [⟨64,199004410,199004528⟩]
theorem checked61425 : checkPrefixCuts (2^48) 8055029761 10 Manual.Count131072.C061425.packed 64 cuts61425 = true := by
 decide +kernel
def cuts61426 : List PrefixCut := [⟨35,108883220,108883281⟩,
⟨64,198826464,198826577⟩]
theorem checked61426 : checkPrefixCuts (2^48) 8055160833 10 Manual.Count131072.C061426.packed 64 cuts61426 = true := by
 decide +kernel
def pointBounds61426 : List (Nat × Nat × Nat) := [(8055232512,114206794724880,114207183297958)]
theorem point_links_checked61426 : (cuts61426.take 1).map (fun c => (8055160833-1+2*2^10*c.k,114206685841660+c.lower,114207074414677+c.upper)) = pointBounds61426 := by
 decide +kernel
def cuts61427 : List PrefixCut := [⟨64,200849893,200850008⟩]
theorem checked61427 : checkPrefixCuts (2^48) 8055291905 10 Manual.Count131072.C061427.packed 64 cuts61427 = true := by
 decide +kernel
def cuts61428 : List PrefixCut := [⟨30,92701536,92701588⟩,
⟨64,198959759,198959874⟩]
theorem checked61428 : checkPrefixCuts (2^48) 8055422977 10 Manual.Count131072.C061428.packed 64 cuts61428 = true := by
 decide +kernel
def pointBounds61428 : List (Nat × Nat × Nat) := [(8055484416,114207178219553,114207566792850)]
theorem point_links_checked61428 : (cuts61428.take 1).map (fun c => (8055422977-1+2*2^10*c.k,114207085518017+c.lower,114207474091262+c.upper)) = pointBounds61428 := by
 decide +kernel
def cuts61429 : List PrefixCut := [⟨64,197733583,197733695⟩]
theorem checked61429 : checkPrefixCuts (2^48) 8055554049 10 Manual.Count131072.C061429.packed 64 cuts61429 = true := by
 decide +kernel
def cuts61430 : List PrefixCut := [⟨25,79805332,79805375⟩,
⟨64,202482316,202482431⟩]
theorem checked61430 : checkPrefixCuts (2^48) 8055685121 10 Manual.Count131072.C061430.packed 64 cuts61430 = true := by
 decide +kernel
def pointBounds61430 : List (Nat × Nat × Nat) := [(8055736320,114207562016691,114207950590206)]
theorem point_links_checked61430 : (cuts61430.take 1).map (fun c => (8055685121-1+2*2^10*c.k,114207482211359+c.lower,114207870784831+c.upper)) = pointBounds61430 := by
 decide +kernel
def cuts61431 : List PrefixCut := [⟨64,201081395,201081509⟩]
theorem checked61431 : checkPrefixCuts (2^48) 8055816193 10 Manual.Count131072.C061431.packed 64 cuts61431 = true := by
 decide +kernel
def cuts61432 : List PrefixCut := [⟨20,63171380,63171419⟩,
⟨64,199331153,199331263⟩]
theorem checked61432 : checkPrefixCuts (2^48) 8055947265 10 Manual.Count131072.C061432.packed 64 cuts61432 = true := by
 decide +kernel
def pointBounds61432 : List (Nat × Nat × Nat) := [(8055988224,114207948946450,114208337520190)]
theorem point_links_checked61432 : (cuts61432.take 1).map (fun c => (8055947265-1+2*2^10*c.k,114207885775070+c.lower,114208274348771+c.upper)) = pointBounds61432 := by
 decide +kernel
def cuts61433 : List PrefixCut := [⟨64,204638644,204638758⟩]
theorem checked61433 : checkPrefixCuts (2^48) 8056078337 10 Manual.Count131072.C061433.packed 64 cuts61433 = true := by
 decide +kernel
def cuts61434 : List PrefixCut := [⟨15,44896368,44896396⟩,
⟨64,198486126,198486245⟩]
theorem checked61434 : checkPrefixCuts (2^48) 8056209409 10 Manual.Count131072.C061434.packed 64 cuts61434 = true := by
 decide +kernel
def pointBounds61434 : List (Nat × Nat × Nat) := [(8056240128,114208334641235,114208723215188)]
theorem point_links_checked61434 : (cuts61434.take 1).map (fun c => (8056209409-1+2*2^10*c.k,114208289744867+c.lower,114208678318792+c.upper)) = pointBounds61434 := by
 decide +kernel
def cuts61435 : List PrefixCut := [⟨64,203304356,203304477⟩]
theorem checked61435 : checkPrefixCuts (2^48) 8056340481 10 Manual.Count131072.C061435.packed 64 cuts61435 = true := by
 decide +kernel
def cuts61436 : List PrefixCut := [⟨10,30989735,30989754⟩,
⟨64,202008363,202008479⟩]
theorem checked61436 : checkPrefixCuts (2^48) 8056471553 10 Manual.Count131072.C061436.packed 64 cuts61436 = true := by
 decide +kernel
def pointBounds61436 : List (Nat × Nat × Nat) := [(8056492032,114208722525084,114209111099268)]
theorem point_links_checked61436 : (cuts61436.take 1).map (fun c => (8056471553-1+2*2^10*c.k,114208691535349+c.lower,114209080109514+c.upper)) = pointBounds61436 := by
 decide +kernel
def cuts61437 : List PrefixCut := [⟨64,200572666,200572784⟩]
theorem checked61437 : checkPrefixCuts (2^48) 8056602625 10 Manual.Count131072.C061437.packed 64 cuts61437 = true := by
 decide +kernel
def cuts61438 : List PrefixCut := [⟨5,15057665,15057675⟩,
⟨64,198263611,198263725⟩]
theorem checked61438 : checkPrefixCuts (2^48) 8056733697 10 Manual.Count131072.C061438.packed 64 cuts61438 = true := by
 decide +kernel
def pointBounds61438 : List (Nat × Nat × Nat) := [(8056743936,114209109174043,114209497748452)]
theorem point_links_checked61438 : (cuts61438.take 1).map (fun c => (8056733697-1+2*2^10*c.k,114209094116378+c.lower,114209482690777+c.upper)) = pointBounds61438 := by
 decide +kernel
def cuts61439 : List PrefixCut := [⟨64,198260371,198260483⟩]
theorem checked61439 : checkPrefixCuts (2^48) 8056864769 10 Manual.Count131072.C061439.packed 64 cuts61439 = true := by
 decide +kernel
def pointBounds61439 : List (Nat × Nat × Nat) := [(8056995840,114209490640360,114209879214985)]
theorem point_links_checked61439 : (cuts61439.take 1).map (fun c => (8056864769-1+2*2^10*c.k,114209292379989+c.lower,114209680954502+c.upper)) = pointBounds61439 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000044
