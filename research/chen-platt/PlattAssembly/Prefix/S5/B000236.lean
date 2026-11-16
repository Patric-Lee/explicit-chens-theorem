import PlattAssemblyKernel
import PlattCertificates.Count131072.C047552
import PlattCertificates.Count131072.C047553
import PlattCertificates.Count131072.C047554
import PlattCertificates.Count131072.C047555
import PlattCertificates.Count131072.C047556
import PlattCertificates.Count131072.C047557
import PlattCertificates.Count131072.C047558
import PlattCertificates.Count131072.C047559
import PlattCertificates.Count131072.C047560
import PlattCertificates.Count131072.C047561
import PlattCertificates.Count131072.C047562
import PlattCertificates.Count131072.C047563
import PlattCertificates.Count131072.C047564
import PlattCertificates.Count131072.C047565
import PlattCertificates.Count131072.C047566
import PlattCertificates.Count131072.C047567
import PlattCertificates.Count131072.C047568
import PlattCertificates.Count131072.C047569
import PlattCertificates.Count131072.C047570
import PlattCertificates.Count131072.C047571
import PlattCertificates.Count131072.C047572
import PlattCertificates.Count131072.C047573
import PlattCertificates.Count131072.C047574
import PlattCertificates.Count131072.C047575
import PlattCertificates.Count131072.C047576
import PlattCertificates.Count131072.C047577
import PlattCertificates.Count131072.C047578
import PlattCertificates.Count131072.C047579
import PlattCertificates.Count131072.C047580
import PlattCertificates.Count131072.C047581
import PlattCertificates.Count131072.C047582
import PlattCertificates.Count131072.C047583
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000236
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts47552 : List PrefixCut := [⟨48,200340521,200340628⟩,
⟨64,265374905,265375048⟩]
theorem checked47552 : checkPrefixCuts (2^48) 6236667905 10 Manual.Count131072.C047552.packed 64 cuts47552 = true := by
 decide +kernel
def pointBounds47552 : List (Nat × Nat × Nat) := [(6236766208,111031682821573,111032069586554)]
theorem point_links_checked47552 : (cuts47552.take 1).map (fun c => (6236667905-1+2*2^10*c.k,111031482481052+c.lower,111031869245926+c.upper)) = pointBounds47552 := by
 decide +kernel
def cuts47553 : List PrefixCut := [⟨64,261803959,261804110⟩]
theorem checked47553 : checkPrefixCuts (2^48) 6236798977 10 Manual.Count131072.C047553.packed 64 cuts47553 = true := by
 decide +kernel
def cuts47554 : List PrefixCut := [⟨16,67921010,67921050⟩,
⟨64,262249762,262249923⟩]
theorem checked47554 : checkPrefixCuts (2^48) 6236930049 10 Manual.Count131072.C047554.packed 64 cuts47554 = true := by
 decide +kernel
def pointBounds47554 : List (Nat × Nat × Nat) := [(6236962816,111032077580926,111032464346134)]
theorem point_links_checked47554 : (cuts47554.take 1).map (fun c => (6236930049-1+2*2^10*c.k,111032009659916+c.lower,111032396425084+c.upper)) = pointBounds47554 := by
 decide +kernel
def cuts47555 : List PrefixCut := [⟨48,196311405,196311520⟩,
⟨64,260709894,260710044⟩]
theorem checked47555 : checkPrefixCuts (2^48) 6237061121 10 Manual.Count131072.C047555.packed 64 cuts47555 = true := by
 decide +kernel
def pointBounds47555 : List (Nat × Nat × Nat) := [(6237159424,111032468221083,111032854986527)]
theorem point_links_checked47555 : (cuts47555.take 1).map (fun c => (6237061121-1+2*2^10*c.k,111032271909678+c.lower,111032658675007+c.upper)) = pointBounds47555 := by
 decide +kernel
def cuts47556 : List PrefixCut := [⟨64,263186445,263186603⟩]
theorem checked47556 : checkPrefixCuts (2^48) 6237192193 10 Manual.Count131072.C047556.packed 64 cuts47556 = true := by
 decide +kernel
def cuts47557 : List PrefixCut := [⟨16,66201891,66201926⟩,
⟨64,262278364,262278517⟩]
theorem checked47557 : checkPrefixCuts (2^48) 6237323265 10 Manual.Count131072.C047557.packed 64 cuts47557 = true := by
 decide +kernel
def pointBounds47557 : List (Nat × Nat × Nat) := [(6237356032,111032862007908,111033248773580)]
theorem point_links_checked47557 : (cuts47557.take 1).map (fun c => (6237323265-1+2*2^10*c.k,111032795806017+c.lower,111033182571654+c.upper)) = pointBounds47557 := by
 decide +kernel
def cuts47558 : List PrefixCut := [⟨48,198104069,198104182⟩,
⟨64,262678999,262679151⟩]
theorem checked47558 : checkPrefixCuts (2^48) 6237454337 10 Manual.Count131072.C047558.packed 64 cuts47558 = true := by
 decide +kernel
def pointBounds47558 : List (Nat × Nat × Nat) := [(6237552640,111033256188450,111033642954353)]
theorem point_links_checked47558 : (cuts47558.take 1).map (fun c => (6237454337-1+2*2^10*c.k,111033058084381+c.lower,111033444850171+c.upper)) = pointBounds47558 := by
 decide +kernel
def cuts47559 : List PrefixCut := [⟨64,261770961,261771111⟩]
theorem checked47559 : checkPrefixCuts (2^48) 6237585409 10 Manual.Count131072.C047559.packed 64 cuts47559 = true := by
 decide +kernel
def cuts47560 : List PrefixCut := [⟨16,65159856,65159890⟩,
⟨64,262848433,262848579⟩]
theorem checked47560 : checkPrefixCuts (2^48) 6237716481 10 Manual.Count131072.C047560.packed 64 cuts47560 = true := by
 decide +kernel
def pointBounds47560 : List (Nat × Nat × Nat) := [(6237749248,111033647694197,111034034460323)]
theorem point_links_checked47560 : (cuts47560.take 1).map (fun c => (6237716481-1+2*2^10*c.k,111033582534341+c.lower,111033969300433+c.upper)) = pointBounds47560 := by
 decide +kernel
def cuts47561 : List PrefixCut := [⟨48,196512259,196512367⟩,
⟨64,263925860,263926006⟩]
theorem checked47561 : checkPrefixCuts (2^48) 6237847553 10 Manual.Count131072.C047561.packed 64 cuts47561 = true := by
 decide +kernel
def pointBounds47561 : List (Nat × Nat × Nat) := [(6237945856,111034041895033,111034428661379)]
theorem point_links_checked47561 : (cuts47561.take 1).map (fun c => (6237847553-1+2*2^10*c.k,111033845382774+c.lower,111034232149012+c.upper)) = pointBounds47561 := by
 decide +kernel
def cuts47562 : List PrefixCut := [⟨64,262702020,262702167⟩]
theorem checked47562 : checkPrefixCuts (2^48) 6237978625 10 Manual.Count131072.C047562.packed 64 cuts47562 = true := by
 decide +kernel
def cuts47563 : List PrefixCut := [⟨16,67727681,67727720⟩,
⟨64,265809902,265810060⟩]
theorem checked47563 : checkPrefixCuts (2^48) 6238109697 10 Manual.Count131072.C047563.packed 64 cuts47563 = true := by
 decide +kernel
def pointBounds47563 : List (Nat × Nat × Nat) := [(6238142464,111034439738335,111034826504905)]
theorem point_links_checked47563 : (cuts47563.take 1).map (fun c => (6238109697-1+2*2^10*c.k,111034372010654+c.lower,111034758777185+c.upper)) = pointBounds47563 := by
 decide +kernel
def cuts47564 : List PrefixCut := [⟨48,196229146,196229262⟩,
⟨64,263097052,263097209⟩]
theorem checked47564 : checkPrefixCuts (2^48) 6238240769 10 Manual.Count131072.C047564.packed 64 cuts47564 = true := by
 decide +kernel
def pointBounds47564 : List (Nat × Nat × Nat) := [(6238339072,111034834049702,111035220816507)]
theorem point_links_checked47564 : (cuts47564.take 1).map (fun c => (6238240769-1+2*2^10*c.k,111034637820556+c.lower,111035024587245+c.upper)) = pointBounds47564 := by
 decide +kernel
def cuts47565 : List PrefixCut := [⟨64,262144038,262144187⟩]
theorem checked47565 : checkPrefixCuts (2^48) 6238371841 10 Manual.Count131072.C047565.packed 64 cuts47565 = true := by
 decide +kernel
def cuts47566 : List PrefixCut := [⟨16,64023670,64023705⟩,
⟨64,258483919,258484065⟩]
theorem checked47566 : checkPrefixCuts (2^48) 6238502913 10 Manual.Count131072.C047566.packed 64 cuts47566 = true := by
 decide +kernel
def pointBounds47566 : List (Nat × Nat × Nat) := [(6238535680,111035227085316,111035613852346)]
theorem point_links_checked47566 : (cuts47566.take 1).map (fun c => (6238502913-1+2*2^10*c.k,111035163061646+c.lower,111035549828641+c.upper)) = pointBounds47566 := by
 decide +kernel
def cuts47567 : List PrefixCut := [⟨48,197164236,197164346⟩,
⟨64,260734377,260734523⟩]
theorem checked47567 : checkPrefixCuts (2^48) 6238633985 10 Manual.Count131072.C047567.packed 64 cuts47567 = true := by
 decide +kernel
def pointBounds47567 : List (Nat × Nat × Nat) := [(6238732288,111035618709801,111036005477052)]
theorem point_links_checked47567 : (cuts47567.take 1).map (fun c => (6238633985-1+2*2^10*c.k,111035421545565+c.lower,111035808312706+c.upper)) = pointBounds47567 := by
 decide +kernel
def cuts47568 : List PrefixCut := [⟨64,264563820,264563970⟩]
theorem checked47568 : checkPrefixCuts (2^48) 6238765057 10 Manual.Count131072.C047568.packed 64 cuts47568 = true := by
 decide +kernel
def cuts47569 : List PrefixCut := [⟨16,65147531,65147567⟩,
⟨64,259956454,259956598⟩]
theorem checked47569 : checkPrefixCuts (2^48) 6238896129 10 Manual.Count131072.C047569.packed 64 cuts47569 = true := by
 decide +kernel
def pointBounds47569 : List (Nat × Nat × Nat) := [(6238928896,111036011991293,111036398758766)]
theorem point_links_checked47569 : (cuts47569.take 1).map (fun c => (6238896129-1+2*2^10*c.k,111035946843762+c.lower,111036333611199+c.upper)) = pointBounds47569 := by
 decide +kernel
def cuts47570 : List PrefixCut := [⟨48,197648101,197648216⟩,
⟨64,264101553,264101707⟩]
theorem checked47570 : checkPrefixCuts (2^48) 6239027201 10 Manual.Count131072.C047570.packed 64 cuts47570 = true := by
 decide +kernel
def pointBounds47570 : List (Nat × Nat × Nat) := [(6239125504,111036404448317,111036791216013)]
theorem point_links_checked47570 : (cuts47570.take 1).map (fun c => (6239027201-1+2*2^10*c.k,111036206800216+c.lower,111036593567797+c.upper)) = pointBounds47570 := by
 decide +kernel
def cuts47571 : List PrefixCut := [⟨64,258231217,258231364⟩]
theorem checked47571 : checkPrefixCuts (2^48) 6239158273 10 Manual.Count131072.C047571.packed 64 cuts47571 = true := by
 decide +kernel
def cuts47572 : List PrefixCut := [⟨16,67173521,67173560⟩,
⟨64,264541593,264541748⟩]
theorem checked47572 : checkPrefixCuts (2^48) 6239289345 10 Manual.Count131072.C047572.packed 64 cuts47572 = true := by
 decide +kernel
def pointBounds47572 : List (Nat × Nat × Nat) := [(6239322112,111036796306507,111037183074428)]
theorem point_links_checked47572 : (cuts47572.take 1).map (fun c => (6239289345-1+2*2^10*c.k,111036729132986+c.lower,111037115900868+c.upper)) = pointBounds47572 := by
 decide +kernel
def cuts47573 : List PrefixCut := [⟨48,193304878,193304997⟩,
⟨64,257363233,257363387⟩]
theorem checked47573 : checkPrefixCuts (2^48) 6239420417 10 Manual.Count131072.C047573.packed 64 cuts47573 = true := by
 decide +kernel
def pointBounds47573 : List (Nat × Nat × Nat) := [(6239518720,111037186979457,111037573747613)]
theorem point_links_checked47573 : (cuts47573.take 1).map (fun c => (6239420417-1+2*2^10*c.k,111036993674579+c.lower,111037380442616+c.upper)) = pointBounds47573 := by
 decide +kernel
def cuts47574 : List PrefixCut := [⟨64,262004238,262004393⟩]
theorem checked47574 : checkPrefixCuts (2^48) 6239551489 10 Manual.Count131072.C047574.packed 64 cuts47574 = true := by
 decide +kernel
def cuts47575 : List PrefixCut := [⟨16,65409982,65410020⟩,
⟨64,261953658,261953808⟩]
theorem checked47575 : checkPrefixCuts (2^48) 6239682561 10 Manual.Count131072.C047575.packed 64 cuts47575 = true := by
 decide +kernel
def pointBounds47575 : List (Nat × Nat × Nat) := [(6239715328,111037578452032,111037965220416)]
theorem point_links_checked47575 : (cuts47575.take 1).map (fun c => (6239682561-1+2*2^10*c.k,111037513042050+c.lower,111037899810396+c.upper)) = pointBounds47575 := by
 decide +kernel
def cuts47576 : List PrefixCut := [⟨48,198660683,198660794⟩,
⟨64,266188368,266188519⟩]
theorem checked47576 : checkPrefixCuts (2^48) 6239813633 10 Manual.Count131072.C047576.packed 64 cuts47576 = true := by
 decide +kernel
def pointBounds47576 : List (Nat × Nat × Nat) := [(6239911936,111037973656391,111038360424998)]
theorem point_links_checked47576 : (cuts47576.take 1).map (fun c => (6239813633-1+2*2^10*c.k,111037774995708+c.lower,111038161764204+c.upper)) = pointBounds47576 := by
 decide +kernel
def cuts47577 : List PrefixCut := [⟨64,261671965,261672116⟩]
theorem checked47577 : checkPrefixCuts (2^48) 6239944705 10 Manual.Count131072.C047577.packed 64 cuts47577 = true := by
 decide +kernel
def cuts47578 : List PrefixCut := [⟨16,64864573,64864609⟩,
⟨64,262207763,262207915⟩]
theorem checked47578 : checkPrefixCuts (2^48) 6240075777 10 Manual.Count131072.C047578.packed 64 cuts47578 = true := by
 decide +kernel
def pointBounds47578 : List (Nat × Nat × Nat) := [(6240108544,111038367720614,111038754489448)]
theorem point_links_checked47578 : (cuts47578.take 1).map (fun c => (6240075777-1+2*2^10*c.k,111038302856041+c.lower,111038689624839+c.upper)) = pointBounds47578 := by
 decide +kernel
def cuts47579 : List PrefixCut := [⟨48,196979234,196979347⟩,
⟨64,263690759,263690908⟩]
theorem checked47579 : checkPrefixCuts (2^48) 6240206849 10 Manual.Count131072.C047579.packed 64 cuts47579 = true := by
 decide +kernel
def pointBounds47579 : List (Nat × Nat × Nat) := [(6240305152,111038762043038,111039148812101)]
theorem point_links_checked47579 : (cuts47579.take 1).map (fun c => (6240206849-1+2*2^10*c.k,111038565063804+c.lower,111038951832754+c.upper)) = pointBounds47579 := by
 decide +kernel
def cuts47580 : List PrefixCut := [⟨64,258904078,258904230⟩]
theorem checked47580 : checkPrefixCuts (2^48) 6240337921 10 Manual.Count131072.C047580.packed 64 cuts47580 = true := by
 decide +kernel
def cuts47581 : List PrefixCut := [⟨16,65672365,65672405⟩,
⟨64,261289177,261289330⟩]
theorem checked47581 : checkPrefixCuts (2^48) 6240468993 10 Manual.Count131072.C047581.packed 64 cuts47581 = true := by
 decide +kernel
def pointBounds47581 : List (Nat × Nat × Nat) := [(6240501760,111039153331006,111039540100297)]
theorem point_links_checked47581 : (cuts47581.take 1).map (fun c => (6240468993-1+2*2^10*c.k,111039087658641+c.lower,111039474427892+c.upper)) = pointBounds47581 := by
 decide +kernel
def cuts47582 : List PrefixCut := [⟨48,198635644,198635759⟩,
⟨64,266019510,266019665⟩]
theorem checked47582 : checkPrefixCuts (2^48) 6240600065 10 Manual.Count131072.C047582.packed 64 cuts47582 = true := by
 decide +kernel
def pointBounds47582 : List (Nat × Nat × Nat) := [(6240698368,111039547583462,111039934352981)]
theorem point_links_checked47582 : (cuts47582.take 1).map (fun c => (6240600065-1+2*2^10*c.k,111039348947818+c.lower,111039735717222+c.upper)) = pointBounds47582 := by
 decide +kernel
def cuts47583 : List PrefixCut := [⟨64,259609423,259609575⟩]
theorem checked47583 : checkPrefixCuts (2^48) 6240731137 10 Manual.Count131072.C047583.packed 64 cuts47583 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000236
