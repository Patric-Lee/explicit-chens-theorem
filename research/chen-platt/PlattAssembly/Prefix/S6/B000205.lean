import PlattAssemblyKernel
import PlattCertificates.Count131072.C056560
import PlattCertificates.Count131072.C056561
import PlattCertificates.Count131072.C056562
import PlattCertificates.Count131072.C056563
import PlattCertificates.Count131072.C056564
import PlattCertificates.Count131072.C056565
import PlattCertificates.Count131072.C056566
import PlattCertificates.Count131072.C056567
import PlattCertificates.Count131072.C056568
import PlattCertificates.Count131072.C056569
import PlattCertificates.Count131072.C056570
import PlattCertificates.Count131072.C056571
import PlattCertificates.Count131072.C056572
import PlattCertificates.Count131072.C056573
import PlattCertificates.Count131072.C056574
import PlattCertificates.Count131072.C056575
import PlattCertificates.Count131072.C056576
import PlattCertificates.Count131072.C056577
import PlattCertificates.Count131072.C056578
import PlattCertificates.Count131072.C056579
import PlattCertificates.Count131072.C056580
import PlattCertificates.Count131072.C056581
import PlattCertificates.Count131072.C056582
import PlattCertificates.Count131072.C056583
import PlattCertificates.Count131072.C056584
import PlattCertificates.Count131072.C056585
import PlattCertificates.Count131072.C056586
import PlattCertificates.Count131072.C056587
import PlattCertificates.Count131072.C056588
import PlattCertificates.Count131072.C056589
import PlattCertificates.Count131072.C056590
import PlattCertificates.Count131072.C056591
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000205
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts56560 : List PrefixCut := [⟨64,218768889,218769009⟩]
theorem checked56560 : checkPrefixCuts (2^48) 7417364481 10 Manual.Count131072.C056560.packed 64 cuts56560 = true := by
 decide +kernel
def cuts56561 : List PrefixCut := [⟨42,144085555,144085636⟩,
⟨64,219865464,219865587⟩]
theorem checked56561 : checkPrefixCuts (2^48) 7417495553 10 Manual.Count131072.C056561.packed 64 cuts56561 = true := by
 decide +kernel
def pointBounds56561 : List (Nat × Nat × Nat) := [(7417581568,113187299807959,113187687799457)]
theorem point_links_checked56561 : (cuts56561.take 1).map (fun c => (7417495553-1+2*2^10*c.k,113187155722404+c.lower,113187543713821+c.upper)) = pointBounds56561 := by
 decide +kernel
def cuts56562 : List PrefixCut := [⟨64,220430774,220430899⟩]
theorem checked56562 : checkPrefixCuts (2^48) 7417626625 10 Manual.Count131072.C056562.packed 64 cuts56562 = true := by
 decide +kernel
def cuts56563 : List PrefixCut := [⟨28,95737610,95737666⟩,
⟨64,220730442,220730568⟩]
theorem checked56563 : checkPrefixCuts (2^48) 7417757697 10 Manual.Count131072.C056563.packed 64 cuts56563 = true := by
 decide +kernel
def pointBounds56563 : List (Nat × Nat × Nat) := [(7417815040,113187691756252,113188079747973)]
theorem point_links_checked56563 : (cuts56563.take 1).map (fun c => (7417757697-1+2*2^10*c.k,113187596018642+c.lower,113187984010307+c.upper)) = pointBounds56563 := by
 decide +kernel
def cuts56564 : List PrefixCut := [⟨64,219512310,219512434⟩]
theorem checked56564 : checkPrefixCuts (2^48) 7417888769 10 Manual.Count131072.C056564.packed 64 cuts56564 = true := by
 decide +kernel
def cuts56565 : List PrefixCut := [⟨14,48531242,48531268⟩,
⟨64,218673654,218673776⟩]
theorem checked56565 : checkPrefixCuts (2^48) 7418019841 10 Manual.Count131072.C056565.packed 64 cuts56565 = true := by
 decide +kernel
def pointBounds56565 : List (Nat × Nat × Nat) := [(7418048512,113188084792636,113188472784577)]
theorem point_links_checked56565 : (cuts56565.take 1).map (fun c => (7418019841-1+2*2^10*c.k,113188036261394+c.lower,113188424253309+c.upper)) = pointBounds56565 := by
 decide +kernel
def cuts56566 : List PrefixCut := [⟨64,219087162,219087287⟩]
theorem checked56566 : checkPrefixCuts (2^48) 7418150913 10 Manual.Count131072.C056566.packed 64 cuts56566 = true := by
 decide +kernel
def pointBounds56566 : List (Nat × Nat × Nat) := [(7418281984,113188474022210,113188862014372)]
theorem point_links_checked56566 : (cuts56566.take 1).map (fun c => (7418150913-1+2*2^10*c.k,113188254935048+c.lower,113188642927085+c.upper)) = pointBounds56566 := by
 decide +kernel
def cuts56567 : List PrefixCut := [⟨64,219576559,219576685⟩]
theorem checked56567 : checkPrefixCuts (2^48) 7418281985 10 Manual.Count131072.C056567.packed 64 cuts56567 = true := by
 decide +kernel
def cuts56568 : List PrefixCut := [⟨50,171234376,171234471⟩,
⟨64,218244687,218244809⟩]
theorem checked56568 : checkPrefixCuts (2^48) 7418413057 10 Manual.Count131072.C056568.packed 64 cuts56568 = true := by
 decide +kernel
def pointBounds56568 : List (Nat × Nat × Nat) := [(7418515456,113188864833145,113189252825528)]
theorem point_links_checked56568 : (cuts56568.take 1).map (fun c => (7418413057-1+2*2^10*c.k,113188693598769+c.lower,113189081591057+c.upper)) = pointBounds56568 := by
 decide +kernel
def cuts56569 : List PrefixCut := [⟨64,221086493,221086619⟩]
theorem checked56569 : checkPrefixCuts (2^48) 7418544129 10 Manual.Count131072.C056569.packed 64 cuts56569 = true := by
 decide +kernel
def cuts56570 : List PrefixCut := [⟨36,123915991,123916061⟩,
⟨64,220209926,220210049⟩]
theorem checked56570 : checkPrefixCuts (2^48) 7418675201 10 Manual.Count131072.C056570.packed 64 cuts56570 = true := by
 decide +kernel
def pointBounds56570 : List (Nat × Nat × Nat) := [(7418748928,113189256845940,113189644838546)]
theorem point_links_checked56570 : (cuts56570.take 1).map (fun c => (7418675201-1+2*2^10*c.k,113189132929949+c.lower,113189520922485+c.upper)) = pointBounds56570 := by
 decide +kernel
def cuts56571 : List PrefixCut := [⟨64,216411997,216412120⟩]
theorem checked56571 : checkPrefixCuts (2^48) 7418806273 10 Manual.Count131072.C056571.packed 64 cuts56571 = true := by
 decide +kernel
def cuts56572 : List PrefixCut := [⟨22,76259284,76259328⟩,
⟨64,222554413,222554539⟩]
theorem checked56572 : checkPrefixCuts (2^48) 7418937345 10 Manual.Count131072.C056572.packed 64 cuts56572 = true := by
 decide +kernel
def pointBounds56572 : List (Nat × Nat × Nat) := [(7418982400,113189645811156,113190033803982)]
theorem point_links_checked56572 : (cuts56572.take 1).map (fun c => (7418937345-1+2*2^10*c.k,113189569551872+c.lower,113189957544654+c.upper)) = pointBounds56572 := by
 decide +kernel
def cuts56573 : List PrefixCut := [⟨64,219363577,219363703⟩]
theorem checked56573 : checkPrefixCuts (2^48) 7419068417 10 Manual.Count131072.C056573.packed 64 cuts56573 = true := by
 decide +kernel
def cuts56574 : List PrefixCut := [⟨8,26936458,26936473⟩,
⟨64,218107723,218107848⟩]
theorem checked56574 : checkPrefixCuts (2^48) 7419199489 10 Manual.Count131072.C056574.packed 64 cuts56574 = true := by
 decide +kernel
def pointBounds56574 : List (Nat × Nat × Nat) := [(7419215872,113190038406320,113190426399369)]
theorem point_links_checked56574 : (cuts56574.take 1).map (fun c => (7419199489-1+2*2^10*c.k,113190011469862+c.lower,113190399462896+c.upper)) = pointBounds56574 := by
 decide +kernel
def cuts56575 : List PrefixCut := [⟨58,200235397,200235512⟩,
⟨64,220835411,220835537⟩]
theorem checked56575 : checkPrefixCuts (2^48) 7419330561 10 Manual.Count131072.C056575.packed 64 cuts56575 = true := by
 decide +kernel
def pointBounds56575 : List (Nat × Nat × Nat) := [(7419449344,113190429812982,113190817806256)]
theorem point_links_checked56575 : (cuts56575.take 1).map (fun c => (7419330561-1+2*2^10*c.k,113190229577585+c.lower,113190617570744+c.upper)) = pointBounds56575 := by
 decide +kernel
def cuts56576 : List PrefixCut := [⟨64,220072782,220072908⟩]
theorem checked56576 : checkPrefixCuts (2^48) 7419461633 10 Manual.Count131072.C056576.packed 64 cuts56576 = true := by
 decide +kernel
def cuts56577 : List PrefixCut := [⟨44,149887000,149887086⟩,
⟨64,219120452,219120577⟩]
theorem checked56577 : checkPrefixCuts (2^48) 7419592705 10 Manual.Count131072.C056577.packed 64 cuts56577 = true := by
 decide +kernel
def pointBounds56577 : List (Nat × Nat × Nat) := [(7419682816,113190820372778,113191208366275)]
theorem point_links_checked56577 : (cuts56577.take 1).map (fun c => (7419592705-1+2*2^10*c.k,113190670485778+c.lower,113191058479189+c.upper)) = pointBounds56577 := by
 decide +kernel
def cuts56578 : List PrefixCut := [⟨64,217864707,217864828⟩]
theorem checked56578 : checkPrefixCuts (2^48) 7419723777 10 Manual.Count131072.C056578.packed 64 cuts56578 = true := by
 decide +kernel
def cuts56579 : List PrefixCut := [⟨30,103563114,103563175⟩,
⟨64,220136974,220137101⟩]
theorem checked56579 : checkPrefixCuts (2^48) 7419854849 10 Manual.Count131072.C056579.packed 64 cuts56579 = true := by
 decide +kernel
def pointBounds56579 : List (Nat × Nat × Nat) := [(7419916288,113191211034051,113191599027769)]
theorem point_links_checked56579 : (cuts56579.take 1).map (fun c => (7419854849-1+2*2^10*c.k,113191107470937+c.lower,113191495464594+c.upper)) = pointBounds56579 := by
 decide +kernel
def cuts56580 : List PrefixCut := [⟨64,215505105,215505229⟩]
theorem checked56580 : checkPrefixCuts (2^48) 7419985921 10 Manual.Count131072.C056580.packed 64 cuts56580 = true := by
 decide +kernel
def cuts56581 : List PrefixCut := [⟨16,53410988,53411019⟩,
⟨64,216108232,216108354⟩]
theorem checked56581 : checkPrefixCuts (2^48) 7420116993 10 Manual.Count131072.C056581.packed 64 cuts56581 = true := by
 decide +kernel
def pointBounds56581 : List (Nat × Nat × Nat) := [(7420149760,113191596524004,113191984517943)]
theorem point_links_checked56581 : (cuts56581.take 1).map (fun c => (7420116993-1+2*2^10*c.k,113191543113016+c.lower,113191931106924+c.upper)) = pointBounds56581 := by
 decide +kernel
def cuts56582 : List PrefixCut := [⟨64,215269889,215270013⟩]
theorem checked56582 : checkPrefixCuts (2^48) 7420248065 10 Manual.Count131072.C056582.packed 64 cuts56582 = true := by
 decide +kernel
def cuts56583 : List PrefixCut := [⟨2,7396872,7396876⟩,
⟨64,216669592,216669715⟩]
theorem checked56583 : checkPrefixCuts (2^48) 7420379137 10 Manual.Count131072.C056583.packed 64 cuts56583 = true := by
 decide +kernel
def pointBounds56583 : List (Nat × Nat × Nat) := [(7420383232,113191981888009,113192369882167)]
theorem point_links_checked56583 : (cuts56583.take 1).map (fun c => (7420379137-1+2*2^10*c.k,113191974491137+c.lower,113192362485291+c.upper)) = pointBounds56583 := by
 decide +kernel
def cuts56584 : List PrefixCut := [⟨52,180213702,180213806⟩,
⟨64,220914101,220914229⟩]
theorem checked56584 : checkPrefixCuts (2^48) 7420510209 10 Manual.Count131072.C056584.packed 64 cuts56584 = true := by
 decide +kernel
def pointBounds56584 : List (Nat × Nat × Nat) := [(7420616704,113192371374431,113192759368812)]
theorem point_links_checked56584 : (cuts56584.take 1).map (fun c => (7420510209-1+2*2^10*c.k,113192191160729+c.lower,113192579155006+c.upper)) = pointBounds56584 := by
 decide +kernel
def cuts56585 : List PrefixCut := [⟨64,217761918,217762045⟩]
theorem checked56585 : checkPrefixCuts (2^48) 7420641281 10 Manual.Count131072.C056585.packed 64 cuts56585 = true := by
 decide +kernel
def cuts56586 : List PrefixCut := [⟨38,132908379,132908451⟩,
⟨64,220678723,220678846⟩]
theorem checked56586 : checkPrefixCuts (2^48) 7420772353 10 Manual.Count131072.C056586.packed 64 cuts56586 = true := by
 decide +kernel
def pointBounds56586 : List (Nat × Nat × Nat) := [(7420850176,113192762745127,113193150739731)]
theorem point_links_checked56586 : (cuts56586.take 1).map (fun c => (7420772353-1+2*2^10*c.k,113192629836748+c.lower,113193017831280+c.upper)) = pointBounds56586 := by
 decide +kernel
def cuts56587 : List PrefixCut := [⟨64,215819829,215819950⟩]
theorem checked56587 : checkPrefixCuts (2^48) 7420903425 10 Manual.Count131072.C056587.packed 64 cuts56587 = true := by
 decide +kernel
def cuts56588 : List PrefixCut := [⟨24,83671835,83671881⟩,
⟨64,218698622,218698744⟩]
theorem checked56588 : checkPrefixCuts (2^48) 7421034497 10 Manual.Count131072.C056588.packed 64 cuts56588 = true := by
 decide +kernel
def pointBounds56588 : List (Nat × Nat × Nat) := [(7421083648,113193150007135,113193538001957)]
theorem point_links_checked56588 : (cuts56588.take 1).map (fun c => (7421034497-1+2*2^10*c.k,113193066335300+c.lower,113193454330076+c.upper)) = pointBounds56588 := by
 decide +kernel
def cuts56589 : List PrefixCut := [⟨64,219756750,219756874⟩]
theorem checked56589 : checkPrefixCuts (2^48) 7421165569 10 Manual.Count131072.C056589.packed 64 cuts56589 = true := by
 decide +kernel
def cuts56590 : List PrefixCut := [⟨10,33452443,33452463⟩,
⟨64,217666819,217666943⟩]
theorem checked56590 : checkPrefixCuts (2^48) 7421296641 10 Manual.Count131072.C056590.packed 64 cuts56590 = true := by
 decide +kernel
def pointBounds56590 : List (Nat × Nat × Nat) := [(7421317120,113193538243115,113193926238157)]
theorem point_links_checked56590 : (cuts56590.take 1).map (fun c => (7421296641-1+2*2^10*c.k,113193504790672+c.lower,113193892785694+c.upper)) = pointBounds56590 := by
 decide +kernel
def cuts56591 : List PrefixCut := [⟨60,203781815,203781932⟩,
⟨64,217435418,217435543⟩]
theorem checked56591 : checkPrefixCuts (2^48) 7421427713 10 Manual.Count131072.C056591.packed 64 cuts56591 = true := by
 decide +kernel
def pointBounds56591 : List (Nat × Nat × Nat) := [(7421550592,113193926239306,113194314234569)]
theorem point_links_checked56591 : (cuts56591.take 1).map (fun c => (7421427713-1+2*2^10*c.k,113193722457491+c.lower,113194110452637+c.upper)) = pointBounds56591 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000205
