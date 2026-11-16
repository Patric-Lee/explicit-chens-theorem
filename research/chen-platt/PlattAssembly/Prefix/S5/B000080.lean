import PlattAssemblyKernel
import PlattCertificates.Count131072.C042560
import PlattCertificates.Count131072.C042561
import PlattCertificates.Count131072.C042562
import PlattCertificates.Count131072.C042563
import PlattCertificates.Count131072.C042564
import PlattCertificates.Count131072.C042565
import PlattCertificates.Count131072.C042566
import PlattCertificates.Count131072.C042567
import PlattCertificates.Count131072.C042568
import PlattCertificates.Count131072.C042569
import PlattCertificates.Count131072.C042570
import PlattCertificates.Count131072.C042571
import PlattCertificates.Count131072.C042572
import PlattCertificates.Count131072.C042573
import PlattCertificates.Count131072.C042574
import PlattCertificates.Count131072.C042575
import PlattCertificates.Count131072.C042576
import PlattCertificates.Count131072.C042577
import PlattCertificates.Count131072.C042578
import PlattCertificates.Count131072.C042579
import PlattCertificates.Count131072.C042580
import PlattCertificates.Count131072.C042581
import PlattCertificates.Count131072.C042582
import PlattCertificates.Count131072.C042583
import PlattCertificates.Count131072.C042584
import PlattCertificates.Count131072.C042585
import PlattCertificates.Count131072.C042586
import PlattCertificates.Count131072.C042587
import PlattCertificates.Count131072.C042588
import PlattCertificates.Count131072.C042589
import PlattCertificates.Count131072.C042590
import PlattCertificates.Count131072.C042591
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000080
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts42560 : List PrefixCut := [⟨64,292546392,292546560⟩]
theorem checked42560 : checkPrefixCuts (2^48) 5582356481 10 Manual.Count131072.C042560.packed 64 cuts42560 = true := by
 decide +kernel
def pointBounds42560 : List (Nat × Nat × Nat) := [(5582487552,109645045790754,109645431755189)]
theorem point_links_checked42560 : (cuts42560.take 1).map (fun c => (5582356481-1+2*2^10*c.k,109644753244362+c.lower,109645139208629+c.upper)) = pointBounds42560 := by
 decide +kernel
def cuts42561 : List PrefixCut := [⟨64,297379876,297380053⟩]
theorem checked42561 : checkPrefixCuts (2^48) 5582487553 10 Manual.Count131072.C042561.packed 64 cuts42561 = true := by
 decide +kernel
def cuts42562 : List PrefixCut := [⟨22,101696468,101696528⟩,
⟨64,298784619,298784790⟩]
theorem checked42562 : checkPrefixCuts (2^48) 5582618625 10 Manual.Count131072.C042562.packed 64 cuts42562 = true := by
 decide +kernel
def pointBounds42562 : List (Nat × Nat × Nat) := [(5582663680,109645444867098,109645830831770)]
theorem point_links_checked42562 : (cuts42562.take 1).map (fun c => (5582618625-1+2*2^10*c.k,109645343170630+c.lower,109645729135242+c.upper)) = pointBounds42562 := by
 decide +kernel
def cuts42563 : List PrefixCut := [⟨44,203790690,203790808⟩,
⟨64,295550884,295551057⟩]
theorem checked42563 : checkPrefixCuts (2^48) 5582749697 10 Manual.Count131072.C042563.packed 64 cuts42563 = true := by
 decide +kernel
def pointBounds42563 : List (Nat × Nat × Nat) := [(5582839808,109645845745939,109646231710840)]
theorem point_links_checked42563 : (cuts42563.take 1).map (fun c => (5582749697-1+2*2^10*c.k,109645641955249+c.lower,109646027920032+c.upper)) = pointBounds42563 := by
 decide +kernel
def cuts42564 : List PrefixCut := [⟨64,292871816,292871986⟩]
theorem checked42564 : checkPrefixCuts (2^48) 5582880769 10 Manual.Count131072.C042564.packed 64 cuts42564 = true := by
 decide +kernel
def cuts42565 : List PrefixCut := [⟨2,10335341,10335347⟩,
⟨64,292512052,292512219⟩]
theorem checked42565 : checkPrefixCuts (2^48) 5583011841 10 Manual.Count131072.C042565.packed 64 cuts42565 = true := by
 decide +kernel
def pointBounds42565 : List (Nat × Nat × Nat) := [(5583015936,109646240713290,109646626678422)]
theorem point_links_checked42565 : (cuts42565.take 1).map (fun c => (5583011841-1+2*2^10*c.k,109646230377949+c.lower,109646616343075+c.upper)) = pointBounds42565 := by
 decide +kernel
def cuts42566 : List PrefixCut := [⟨24,112425250,112425317⟩,
⟨64,297597048,297597219⟩]
theorem checked42566 : checkPrefixCuts (2^48) 5583142913 10 Manual.Count131072.C042566.packed 64 cuts42566 = true := by
 decide +kernel
def pointBounds42566 : List (Nat × Nat × Nat) := [(5583192064,109646635315251,109647021280611)]
theorem point_links_checked42566 : (cuts42566.take 1).map (fun c => (5583142913-1+2*2^10*c.k,109646522890001+c.lower,109646908855294+c.upper)) = pointBounds42566 := by
 decide +kernel
def cuts42567 : List PrefixCut := [⟨46,216374868,216374993⟩,
⟨64,299253732,299253908⟩]
theorem checked42567 : checkPrefixCuts (2^48) 5583273985 10 Manual.Count131072.C042567.packed 64 cuts42567 = true := by
 decide +kernel
def pointBounds42567 : List (Nat × Nat × Nat) := [(5583368192,109647036861917,109647422827506)]
theorem point_links_checked42567 : (cuts42567.take 1).map (fun c => (5583273985-1+2*2^10*c.k,109646820487049+c.lower,109647206452513+c.upper)) = pointBounds42567 := by
 decide +kernel
def cuts42568 : List PrefixCut := [⟨64,295616973,295617147⟩]
theorem checked42568 : checkPrefixCuts (2^48) 5583405057 10 Manual.Count131072.C042568.packed 64 cuts42568 = true := by
 decide +kernel
def cuts42569 : List PrefixCut := [⟨4,19055565,19055575⟩,
⟨64,297828153,297828322⟩]
theorem checked42569 : checkPrefixCuts (2^48) 5583536129 10 Manual.Count131072.C042569.packed 64 cuts42569 = true := by
 decide +kernel
def pointBounds42569 : List (Nat × Nat × Nat) := [(5583544320,109647434413319,109647820379143)]
theorem point_links_checked42569 : (cuts42569.take 1).map (fun c => (5583536129-1+2*2^10*c.k,109647415357754+c.lower,109647801323568+c.upper)) = pointBounds42569 := by
 decide +kernel
def cuts42570 : List PrefixCut := [⟨26,117153211,117153285⟩,
⟨64,289654745,289654927⟩]
theorem checked42570 : checkPrefixCuts (2^48) 5583667201 10 Manual.Count131072.C042570.packed 64 cuts42570 = true := by
 decide +kernel
def pointBounds42570 : List (Nat × Nat × Nat) := [(5583720448,109647830339118,109648216305175)]
theorem point_links_checked42570 : (cuts42570.take 1).map (fun c => (5583667201-1+2*2^10*c.k,109647713185907+c.lower,109648099151890+c.upper)) = pointBounds42570 := by
 decide +kernel
def cuts42571 : List PrefixCut := [⟨48,218925282,218925413⟩,
⟨64,293428580,293428752⟩]
theorem checked42571 : checkPrefixCuts (2^48) 5583798273 10 Manual.Count131072.C042571.packed 64 cuts42571 = true := by
 decide +kernel
def pointBounds42571 : List (Nat × Nat × Nat) := [(5583896576,109648221765934,109648607732230)]
theorem point_links_checked42571 : (cuts42571.take 1).map (fun c => (5583798273-1+2*2^10*c.k,109648002840652+c.lower,109648388806817+c.upper)) = pointBounds42571 := by
 decide +kernel
def cuts42572 : List PrefixCut := [⟨64,296093280,296093457⟩]
theorem checked42572 : checkPrefixCuts (2^48) 5583929345 10 Manual.Count131072.C042572.packed 64 cuts42572 = true := by
 decide +kernel
def cuts42573 : List PrefixCut := [⟨6,26413160,26413175⟩,
⟨64,291247346,291247519⟩]
theorem checked42573 : checkPrefixCuts (2^48) 5584060417 10 Manual.Count131072.C042573.packed 64 cuts42573 = true := by
 decide +kernel
def pointBounds42573 : List (Nat × Nat × Nat) := [(5584072704,109648618775672,109649004742201)]
theorem point_links_checked42573 : (cuts42573.take 1).map (fun c => (5584060417-1+2*2^10*c.k,109648592362512+c.lower,109648978329026+c.upper)) = pointBounds42573 := by
 decide +kernel
def cuts42574 : List PrefixCut := [⟨28,128281763,128281838⟩,
⟨64,293659967,293660140⟩]
theorem checked42574 : checkPrefixCuts (2^48) 5584191489 10 Manual.Count131072.C042574.packed 64 cuts42574 = true := by
 decide +kernel
def pointBounds42574 : List (Nat × Nat × Nat) := [(5584248832,109649011891621,109649397858383)]
theorem point_links_checked42574 : (cuts42574.take 1).map (fun c => (5584191489-1+2*2^10*c.k,109648883609858+c.lower,109649269576545+c.upper)) = pointBounds42574 := by
 decide +kernel
def cuts42575 : List PrefixCut := [⟨50,229439107,229439244⟩,
⟨64,294459530,294459708⟩]
theorem checked42575 : checkPrefixCuts (2^48) 5584322561 10 Manual.Count131072.C042575.packed 64 cuts42575 = true := by
 decide +kernel
def pointBounds42575 : List (Nat × Nat × Nat) := [(5584424960,109649406708932,109649792675929)]
theorem point_links_checked42575 : (cuts42575.take 1).map (fun c => (5584322561-1+2*2^10*c.k,109649177269825+c.lower,109649563236685+c.upper)) = pointBounds42575 := by
 decide +kernel
def cuts42576 : List PrefixCut := [⟨64,294049391,294049564⟩]
theorem checked42576 : checkPrefixCuts (2^48) 5584453633 10 Manual.Count131072.C042576.packed 64 cuts42576 = true := by
 decide +kernel
def cuts42577 : List PrefixCut := [⟨8,36642287,36642308⟩,
⟨64,291824854,291825021⟩]
theorem checked42577 : checkPrefixCuts (2^48) 5584584705 10 Manual.Count131072.C042577.packed 64 cuts42577 = true := by
 decide +kernel
def pointBounds42577 : List (Nat × Nat × Nat) := [(5584601088,109649802421033,109650188388265)]
theorem point_links_checked42577 : (cuts42577.take 1).map (fun c => (5584584705-1+2*2^10*c.k,109649765778746+c.lower,109650151745957+c.upper)) = pointBounds42577 := by
 decide +kernel
def cuts42578 : List PrefixCut := [⟨30,141978661,141978739⟩,
⟨64,297513259,297513430⟩]
theorem checked42578 : checkPrefixCuts (2^48) 5584715777 10 Manual.Count131072.C042578.packed 64 cuts42578 = true := by
 decide +kernel
def pointBounds42578 : List (Nat × Nat × Nat) := [(5584777216,109650199582261,109650585549717)]
theorem point_links_checked42578 : (cuts42578.take 1).map (fun c => (5584715777-1+2*2^10*c.k,109650057603600+c.lower,109650443570978+c.upper)) = pointBounds42578 := by
 decide +kernel
def cuts42579 : List PrefixCut := [⟨52,238438940,238439081⟩,
⟨64,292919915,292920088⟩]
theorem checked42579 : checkPrefixCuts (2^48) 5584846849 10 Manual.Count131072.C042579.packed 64 cuts42579 = true := by
 decide +kernel
def pointBounds42579 : List (Nat × Nat × Nat) := [(5584953344,109650593555799,109650979523489)]
theorem point_links_checked42579 : (cuts42579.take 1).map (fun c => (5584846849-1+2*2^10*c.k,109650355116859+c.lower,109650741084408+c.upper)) = pointBounds42579 := by
 decide +kernel
def cuts42580 : List PrefixCut := [⟨64,294979336,294979508⟩]
theorem checked42580 : checkPrefixCuts (2^48) 5584977921 10 Manual.Count131072.C042580.packed 64 cuts42580 = true := by
 decide +kernel
def cuts42581 : List PrefixCut := [⟨10,45811141,45811164⟩,
⟨64,294266882,294267050⟩]
theorem checked42581 : checkPrefixCuts (2^48) 5585108993 10 Manual.Count131072.C042581.packed 64 cuts42581 = true := by
 decide +kernel
def pointBounds42581 : List (Nat × Nat × Nat) := [(5585129472,109650988827251,109651374795168)]
theorem point_links_checked42581 : (cuts42581.take 1).map (fun c => (5585108993-1+2*2^10*c.k,109650943016110+c.lower,109651328984004+c.upper)) = pointBounds42581 := by
 decide +kernel
def cuts42582 : List PrefixCut := [⟨32,147710406,147710496⟩,
⟨64,293252077,293252251⟩]
theorem checked42582 : checkPrefixCuts (2^48) 5585240065 10 Manual.Count131072.C042582.packed 64 cuts42582 = true := by
 decide +kernel
def pointBounds42582 : List (Nat × Nat × Nat) := [(5585305600,109651384993398,109651770961550)]
theorem point_links_checked42582 : (cuts42582.take 1).map (fun c => (5585240065-1+2*2^10*c.k,109651237282992+c.lower,109651623251054+c.upper)) = pointBounds42582 := by
 decide +kernel
def cuts42583 : List PrefixCut := [⟨54,248394576,248394725⟩,
⟨64,294706599,294706774⟩]
theorem checked42583 : checkPrefixCuts (2^48) 5585371137 10 Manual.Count131072.C042583.packed 64 cuts42583 = true := by
 decide +kernel
def pointBounds42583 : List (Nat × Nat × Nat) := [(5585481728,109651778929645,109652164898030)]
theorem point_links_checked42583 : (cuts42583.take 1).map (fun c => (5585371137-1+2*2^10*c.k,109651530535069+c.lower,109651916503305+c.upper)) = pointBounds42583 := by
 decide +kernel
def cuts42584 : List PrefixCut := [⟨64,295657161,295657334⟩]
theorem checked42584 : checkPrefixCuts (2^48) 5585502209 10 Manual.Count131072.C042584.packed 64 cuts42584 = true := by
 decide +kernel
def cuts42585 : List PrefixCut := [⟨12,53920020,53920052⟩,
⟨64,292677095,292677268⟩]
theorem checked42585 : checkPrefixCuts (2^48) 5585633281 10 Manual.Count131072.C042585.packed 64 cuts42585 = true := by
 decide +kernel
def pointBounds42585 : List (Nat × Nat × Nat) := [(5585657856,109652174818849,109652560787465)]
theorem point_links_checked42585 : (cuts42585.take 1).map (fun c => (5585633281-1+2*2^10*c.k,109652120898829+c.lower,109652506867413+c.upper)) = pointBounds42585 := by
 decide +kernel
def cuts42586 : List PrefixCut := [⟨34,157724333,157724423⟩,
⟨64,293426147,293426314⟩]
theorem checked42586 : checkPrefixCuts (2^48) 5585764353 10 Manual.Count131072.C042586.packed 64 cuts42586 = true := by
 decide +kernel
def pointBounds42586 : List (Nat × Nat × Nat) := [(5585833984,109652571300257,109652957269104)]
theorem point_links_checked42586 : (cuts42586.take 1).map (fun c => (5585764353-1+2*2^10*c.k,109652413575924+c.lower,109652799544681+c.upper)) = pointBounds42586 := by
 decide +kernel
def cuts42587 : List PrefixCut := [⟨56,262782663,262782813⟩,
⟨64,301279998,301280169⟩]
theorem checked42587 : checkPrefixCuts (2^48) 5585895425 10 Manual.Count131072.C042587.packed 64 cuts42587 = true := by
 decide +kernel
def pointBounds42587 : List (Nat × Nat × Nat) := [(5586010112,109652969784734,109653355753808)]
theorem point_links_checked42587 : (cuts42587.take 1).map (fun c => (5585895425-1+2*2^10*c.k,109652707002071+c.lower,109653092970995+c.upper)) = pointBounds42587 := by
 decide +kernel
def cuts42588 : List PrefixCut := [⟨64,295579045,295579215⟩]
theorem checked42588 : checkPrefixCuts (2^48) 5586026497 10 Manual.Count131072.C042588.packed 64 cuts42588 = true := by
 decide +kernel
def cuts42589 : List PrefixCut := [⟨14,64395604,64395643⟩,
⟨64,290734939,290735106⟩]
theorem checked42589 : checkPrefixCuts (2^48) 5586157569 10 Manual.Count131072.C042589.packed 64 cuts42589 = true := by
 decide +kernel
def pointBounds42589 : List (Nat × Nat × Nat) := [(5586186240,109653368256718,109653754226022)]
theorem point_links_checked42589 : (cuts42589.take 1).map (fun c => (5586157569-1+2*2^10*c.k,109653303861114+c.lower,109653689830379+c.upper)) = pointBounds42589 := by
 decide +kernel
def cuts42590 : List PrefixCut := [⟨36,164209315,164209408⟩,
⟨64,294456665,294456831⟩]
theorem checked42590 : checkPrefixCuts (2^48) 5586288641 10 Manual.Count131072.C042590.packed 64 cuts42590 = true := by
 decide +kernel
def pointBounds42590 : List (Nat × Nat × Nat) := [(5586362368,109653758805368,109654144774893)]
theorem point_links_checked42590 : (cuts42590.take 1).map (fun c => (5586288641-1+2*2^10*c.k,109653594596053+c.lower,109653980565485+c.upper)) = pointBounds42590 := by
 decide +kernel
def cuts42591 : List PrefixCut := [⟨58,263916750,263916900⟩,
⟨64,291880112,291880279⟩]
theorem checked42591 : checkPrefixCuts (2^48) 5586419713 10 Manual.Count131072.C042591.packed 64 cuts42591 = true := by
 decide +kernel
def pointBounds42591 : List (Nat × Nat × Nat) := [(5586538496,109654152969468,109654538939216)]
theorem point_links_checked42591 : (cuts42591.take 1).map (fun c => (5586419713-1+2*2^10*c.k,109653889052718+c.lower,109654275022316+c.upper)) = pointBounds42591 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000080
