import PlattAssemblyKernel
import PlattCertificates.Count131072.C070608
import PlattCertificates.Count131072.C070609
import PlattCertificates.Count131072.C070610
import PlattCertificates.Count131072.C070611
import PlattCertificates.Count131072.C070612
import PlattCertificates.Count131072.C070613
import PlattCertificates.Count131072.C070614
import PlattCertificates.Count131072.C070615
import PlattCertificates.Count131072.C070616
import PlattCertificates.Count131072.C070617
import PlattCertificates.Count131072.C070618
import PlattCertificates.Count131072.C070619
import PlattCertificates.Count131072.C070620
import PlattCertificates.Count131072.C070621
import PlattCertificates.Count131072.C070622
import PlattCertificates.Count131072.C070623
import PlattCertificates.Count131072.C070624
import PlattCertificates.Count131072.C070625
import PlattCertificates.Count131072.C070626
import PlattCertificates.Count131072.C070627
import PlattCertificates.Count131072.C070628
import PlattCertificates.Count131072.C070629
import PlattCertificates.Count131072.C070630
import PlattCertificates.Count131072.C070631
import PlattCertificates.Count131072.C070632
import PlattCertificates.Count131072.C070633
import PlattCertificates.Count131072.C070634
import PlattCertificates.Count131072.C070635
import PlattCertificates.Count131072.C070636
import PlattCertificates.Count131072.C070637
import PlattCertificates.Count131072.C070638
import PlattCertificates.Count131072.C070639
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000019
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts70608 : List PrefixCut := [⟨37,99928479,99928539⟩,
⟨64,173042655,173042755⟩]
theorem checked70608 : checkPrefixCuts (2^48) 9258663937 10 Manual.Count131072.C070608.packed 64 cuts70608 = true := by
 decide +kernel
def pointBounds70608 : List (Nat × Nat × Nat) := [(9258739712,115919881544477,115920271112163)]
theorem point_links_checked70608 : (cuts70608.take 1).map (fun c => (9258663937-1+2*2^10*c.k,115919781615998+c.lower,115920171183624+c.upper)) = pointBounds70608 := by
 decide +kernel
def cuts70609 : List PrefixCut := [⟨64,173101004,173101102⟩]
theorem checked70609 : checkPrefixCuts (2^48) 9258795009 10 Manual.Count131072.C070609.packed 64 cuts70609 = true := by
 decide +kernel
def cuts70610 : List PrefixCut := [⟨51,137986557,137986640⟩,
⟨64,172125751,172125856⟩]
theorem checked70610 : checkPrefixCuts (2^48) 9258926081 10 Manual.Count131072.C070610.packed 64 cuts70610 = true := by
 decide +kernel
def pointBounds70610 : List (Nat × Nat × Nat) := [(9259030528,115920265746214,115920655314121)]
theorem point_links_checked70610 : (cuts70610.take 1).map (fun c => (9258926081-1+2*2^10*c.k,115920127759657+c.lower,115920517327481+c.upper)) = pointBounds70610 := by
 decide +kernel
def cuts70611 : List PrefixCut := [⟨64,175436877,175436983⟩]
theorem checked70611 : checkPrefixCuts (2^48) 9259057153 10 Manual.Count131072.C070611.packed 64 cuts70611 = true := by
 decide +kernel
def cuts70612 : List PrefixCut := [⟨64,175708003,175708111⟩]
theorem checked70612 : checkPrefixCuts (2^48) 9259188225 10 Manual.Count131072.C070612.packed 64 cuts70612 = true := by
 decide +kernel
def cuts70613 : List PrefixCut := [⟨1,2918312,2918314⟩,
⟨64,175097530,175097633⟩]
theorem checked70613 : checkPrefixCuts (2^48) 9259319297 10 Manual.Count131072.C070613.packed 64 cuts70613 = true := by
 decide +kernel
def pointBounds70613 : List (Nat × Nat × Nat) := [(9259321344,115920653948600,115921043516745)]
theorem point_links_checked70613 : (cuts70613.take 1).map (fun c => (9259319297-1+2*2^10*c.k,115920651030288+c.lower,115921040598431+c.upper)) = pointBounds70613 := by
 decide +kernel
def cuts70614 : List PrefixCut := [⟨64,170170498,170170596⟩]
theorem checked70614 : checkPrefixCuts (2^48) 9259450369 10 Manual.Count131072.C070614.packed 64 cuts70614 = true := by
 decide +kernel
def cuts70615 : List PrefixCut := [⟨15,41250330,41250354⟩,
⟨64,174788584,174788688⟩]
theorem checked70615 : checkPrefixCuts (2^48) 9259581441 10 Manual.Count131072.C070615.packed 64 cuts70615 = true := by
 decide +kernel
def pointBounds70615 : List (Nat × Nat × Nat) := [(9259612160,115921037548646,115921427117014)]
theorem point_links_checked70615 : (cuts70615.take 1).map (fun c => (9259581441-1+2*2^10*c.k,115920996298316+c.lower,115921385866660+c.upper)) = pointBounds70615 := by
 decide +kernel
def cuts70616 : List PrefixCut := [⟨64,176305992,176306097⟩]
theorem checked70616 : checkPrefixCuts (2^48) 9259712513 10 Manual.Count131072.C070616.packed 64 cuts70616 = true := by
 decide +kernel
def cuts70617 : List PrefixCut := [⟨29,77999398,77999450⟩,
⟨64,174631640,174631752⟩]
theorem checked70617 : checkPrefixCuts (2^48) 9259843585 10 Manual.Count131072.C070617.packed 64 cuts70617 = true := by
 decide +kernel
def pointBounds70617 : List (Nat × Nat × Nat) := [(9259902976,115921425392290,115921814960895)]
theorem point_links_checked70617 : (cuts70617.take 1).map (fun c => (9259843585-1+2*2^10*c.k,115921347392892+c.lower,115921736961445+c.upper)) = pointBounds70617 := by
 decide +kernel
def cuts70618 : List PrefixCut := [⟨64,174477201,174477303⟩]
theorem checked70618 : checkPrefixCuts (2^48) 9259974657 10 Manual.Count131072.C070618.packed 64 cuts70618 = true := by
 decide +kernel
def cuts70619 : List PrefixCut := [⟨43,116539658,116539733⟩,
⟨64,172894118,172894228⟩]
theorem checked70619 : checkPrefixCuts (2^48) 9260105729 10 Manual.Count131072.C070619.packed 64 cuts70619 = true := by
 decide +kernel
def pointBounds70619 : List (Nat × Nat × Nat) := [(9260193792,115921813041391,115922202610233)]
theorem point_links_checked70619 : (cuts70619.take 1).map (fun c => (9260105729-1+2*2^10*c.k,115921696501733+c.lower,115922086070500+c.upper)) = pointBounds70619 := by
 decide +kernel
def cuts70620 : List PrefixCut := [⟨64,173286831,173286930⟩]
theorem checked70620 : checkPrefixCuts (2^48) 9260236801 10 Manual.Count131072.C070620.packed 64 cuts70620 = true := by
 decide +kernel
def cuts70621 : List PrefixCut := [⟨57,154256950,154257040⟩,
⟨64,173405953,173406054⟩]
theorem checked70621 : checkPrefixCuts (2^48) 9260367873 10 Manual.Count131072.C070621.packed 64 cuts70621 = true := by
 decide +kernel
def pointBounds70621 : List (Nat × Nat × Nat) := [(9260484608,115922196939632,115922586508698)]
theorem point_links_checked70621 : (cuts70621.take 1).map (fun c => (9260367873-1+2*2^10*c.k,115922042682682+c.lower,115922432251658+c.upper)) = pointBounds70621 := by
 decide +kernel
def cuts70622 : List PrefixCut := [⟨64,172977957,172978058⟩]
theorem checked70622 : checkPrefixCuts (2^48) 9260498945 10 Manual.Count131072.C070622.packed 64 cuts70622 = true := by
 decide +kernel
def cuts70623 : List PrefixCut := [⟨64,173674591,173674697⟩]
theorem checked70623 : checkPrefixCuts (2^48) 9260630017 10 Manual.Count131072.C070623.packed 64 cuts70623 = true := by
 decide +kernel
def cuts70624 : List PrefixCut := [⟨7,19087642,19087655⟩,
⟨64,173824110,173824209⟩]
theorem checked70624 : checkPrefixCuts (2^48) 9260761089 10 Manual.Count131072.C070624.packed 64 cuts70624 = true := by
 decide +kernel
def pointBounds70624 : List (Nat × Nat × Nat) := [(9260775424,115922581828825,115922971398122)]
theorem point_links_checked70624 : (cuts70624.take 1).map (fun c => (9260761089-1+2*2^10*c.k,115922562741183+c.lower,115922952310467+c.upper)) = pointBounds70624 := by
 decide +kernel
def cuts70625 : List PrefixCut := [⟨64,173943226,173943324⟩]
theorem checked70625 : checkPrefixCuts (2^48) 9260892161 10 Manual.Count131072.C070625.packed 64 cuts70625 = true := by
 decide +kernel
def cuts70626 : List PrefixCut := [⟨21,56683741,56683777⟩,
⟨64,176159472,176159574⟩]
theorem checked70626 : checkPrefixCuts (2^48) 9261023233 10 Manual.Count131072.C070626.packed 64 cuts70626 = true := by
 decide +kernel
def pointBounds70626 : List (Nat × Nat × Nat) := [(9261066240,115922967192260,115923356761777)]
theorem point_links_checked70626 : (cuts70626.take 1).map (fun c => (9261023233-1+2*2^10*c.k,115922910508519+c.lower,115923300078000+c.upper)) = pointBounds70626 := by
 decide +kernel
def cuts70627 : List PrefixCut := [⟨64,173603965,173604070⟩]
theorem checked70627 : checkPrefixCuts (2^48) 9261154305 10 Manual.Count131072.C070627.packed 64 cuts70627 = true := by
 decide +kernel
def cuts70628 : List PrefixCut := [⟨35,96435466,96435522⟩,
⟨64,174695653,174695757⟩]
theorem checked70628 : checkPrefixCuts (2^48) 9261285377 10 Manual.Count131072.C070628.packed 64 cuts70628 = true := by
 decide +kernel
def pointBounds70628 : List (Nat × Nat × Nat) := [(9261357056,115923356707422,115923746277166)]
theorem point_links_checked70628 : (cuts70628.take 1).map (fun c => (9261285377-1+2*2^10*c.k,115923260271956+c.lower,115923649841644+c.upper)) = pointBounds70628 := by
 decide +kernel
def cuts70629 : List PrefixCut := [⟨64,174358860,174358964⟩]
theorem checked70629 : checkPrefixCuts (2^48) 9261416449 10 Manual.Count131072.C070629.packed 64 cuts70629 = true := by
 decide +kernel
def cuts70630 : List PrefixCut := [⟨49,131686862,131686942⟩,
⟨64,173535817,173535920⟩]
theorem checked70630 : checkPrefixCuts (2^48) 9261547521 10 Manual.Count131072.C070630.packed 64 cuts70630 = true := by
 decide +kernel
def pointBounds70630 : List (Nat × Nat × Nat) := [(9261647872,115923741013331,115924130583307)]
theorem point_links_checked70630 : (cuts70630.take 1).map (fun c => (9261547521-1+2*2^10*c.k,115923609326469+c.lower,115923998896365+c.upper)) = pointBounds70630 := by
 decide +kernel
def cuts70631 : List PrefixCut := [⟨64,175539178,175539285⟩]
theorem checked70631 : checkPrefixCuts (2^48) 9261678593 10 Manual.Count131072.C070631.packed 64 cuts70631 = true := by
 decide +kernel
def cuts70632 : List PrefixCut := [⟨63,170218328,170218430⟩,
⟨64,173075034,173075138⟩]
theorem checked70632 : checkPrefixCuts (2^48) 9261809665 10 Manual.Count131072.C070632.packed 64 cuts70632 = true := by
 decide +kernel
def pointBounds70632 : List (Nat × Nat × Nat) := [(9261938688,115924128619792,115924518190000)]
theorem point_links_checked70632 : (cuts70632.take 1).map (fun c => (9261809665-1+2*2^10*c.k,115923958401464+c.lower,115924347971570+c.upper)) = pointBounds70632 := by
 decide +kernel
def cuts70633 : List PrefixCut := [⟨64,174987192,174987291⟩]
theorem checked70633 : checkPrefixCuts (2^48) 9261940737 10 Manual.Count131072.C070633.packed 64 cuts70633 = true := by
 decide +kernel
def cuts70634 : List PrefixCut := [⟨64,173981855,173981955⟩]
theorem checked70634 : checkPrefixCuts (2^48) 9262071809 10 Manual.Count131072.C070634.packed 64 cuts70634 = true := by
 decide +kernel
def cuts70635 : List PrefixCut := [⟨13,36497892,36497911⟩,
⟨64,174587176,174587278⟩]
theorem checked70635 : checkPrefixCuts (2^48) 9262202881 10 Manual.Count131072.C070635.packed 64 cuts70635 = true := by
 decide +kernel
def pointBounds70635 : List (Nat × Nat × Nat) := [(9262229504,115924516943437,115924906513865)]
theorem point_links_checked70635 : (cuts70635.take 1).map (fun c => (9262202881-1+2*2^10*c.k,115924480445545+c.lower,115924870015954+c.upper)) = pointBounds70635 := by
 decide +kernel
def cuts70636 : List PrefixCut := [⟨64,176134546,176134647⟩]
theorem checked70636 : checkPrefixCuts (2^48) 9262333953 10 Manual.Count131072.C070636.packed 64 cuts70636 = true := by
 decide +kernel
def cuts70637 : List PrefixCut := [⟨27,72446601,72446647⟩,
⟨64,172455027,172455135⟩]
theorem checked70637 : checkPrefixCuts (2^48) 9262465025 10 Manual.Count131072.C070637.packed 64 cuts70637 = true := by
 decide +kernel
def pointBounds70637 : List (Nat × Nat × Nat) := [(9262520320,115924903613868,115925293184526)]
theorem point_links_checked70637 : (cuts70637.take 1).map (fun c => (9262465025-1+2*2^10*c.k,115924831167267+c.lower,115925220737879+c.upper)) = pointBounds70637 := by
 decide +kernel
def cuts70638 : List PrefixCut := [⟨64,177041207,177041311⟩]
theorem checked70638 : checkPrefixCuts (2^48) 9262596097 10 Manual.Count131072.C070638.packed 64 cuts70638 = true := by
 decide +kernel
def cuts70639 : List PrefixCut := [⟨41,110064497,110064557⟩,
⟨64,171690458,171690554⟩]
theorem checked70639 : checkPrefixCuts (2^48) 9262727169 10 Manual.Count131072.C070639.packed 64 cuts70639 = true := by
 decide +kernel
def pointBounds70639 : List (Nat × Nat × Nat) := [(9262811136,115925290727998,115925680298882)]
theorem point_links_checked70639 : (cuts70639.take 1).map (fun c => (9262727169-1+2*2^10*c.k,115925180663501+c.lower,115925570234325+c.upper)) = pointBounds70639 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000019
