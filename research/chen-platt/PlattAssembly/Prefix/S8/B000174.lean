import PlattAssemblyKernel
import PlattCertificates.Count131072.C075568
import PlattCertificates.Count131072.C075569
import PlattCertificates.Count131072.C075570
import PlattCertificates.Count131072.C075571
import PlattCertificates.Count131072.C075572
import PlattCertificates.Count131072.C075573
import PlattCertificates.Count131072.C075574
import PlattCertificates.Count131072.C075575
import PlattCertificates.Count131072.C075576
import PlattCertificates.Count131072.C075577
import PlattCertificates.Count131072.C075578
import PlattCertificates.Count131072.C075579
import PlattCertificates.Count131072.C075580
import PlattCertificates.Count131072.C075581
import PlattCertificates.Count131072.C075582
import PlattCertificates.Count131072.C075583
import PlattCertificates.Count131072.C075584
import PlattCertificates.Count131072.C075585
import PlattCertificates.Count131072.C075586
import PlattCertificates.Count131072.C075587
import PlattCertificates.Count131072.C075588
import PlattCertificates.Count131072.C075589
import PlattCertificates.Count131072.C075590
import PlattCertificates.Count131072.C075591
import PlattCertificates.Count131072.C075592
import PlattCertificates.Count131072.C075593
import PlattCertificates.Count131072.C075594
import PlattCertificates.Count131072.C075595
import PlattCertificates.Count131072.C075596
import PlattCertificates.Count131072.C075597
import PlattCertificates.Count131072.C075598
import PlattCertificates.Count131072.C075599
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000174
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts75568 : List PrefixCut := [⟨3,7470937,7470941⟩,
⟨64,160127021,160127110⟩]
theorem checked75568 : checkPrefixCuts (2^48) 9908781057 10 Manual.Count131072.C075568.packed 64 cuts75568 = true := by
 decide +kernel
def pointBounds75568 : List (Nat × Nat × Nat) := [(9908787200,116750972233857,116751362296675)]
theorem point_links_checked75568 : (cuts75568.take 1).map (fun c => (9908781057-1+2*2^10*c.k,116750964762920+c.lower,116751354825734+c.upper)) = pointBounds75568 := by
 decide +kernel
def cuts75569 : List PrefixCut := [⟨64,161431572,161431666⟩]
theorem checked75569 : checkPrefixCuts (2^48) 9908912129 10 Manual.Count131072.C075569.packed 64 cuts75569 = true := by
 decide +kernel
def cuts75570 : List PrefixCut := [⟨27,68060251,68060290⟩,
⟨64,161202190,161202284⟩]
theorem checked75570 : checkPrefixCuts (2^48) 9909043201 10 Manual.Count131072.C075570.packed 64 cuts75570 = true := by
 decide +kernel
def pointBounds75570 : List (Nat × Nat × Nat) := [(9909098496,116751354381764,116751744444800)]
theorem point_links_checked75570 : (cuts75570.take 1).map (fun c => (9909043201-1+2*2^10*c.k,116751286321513+c.lower,116751676384510+c.upper)) = pointBounds75570 := by
 decide +kernel
def cuts75571 : List PrefixCut := [⟨64,161398896,161398995⟩]
theorem checked75571 : checkPrefixCuts (2^48) 9909174273 10 Manual.Count131072.C075571.packed 64 cuts75571 = true := by
 decide +kernel
def cuts75572 : List PrefixCut := [⟨51,128731271,128731352⟩,
⟨64,161112709,161112808⟩]
theorem checked75572 : checkPrefixCuts (2^48) 9909305345 10 Manual.Count131072.C075572.packed 64 cuts75572 = true := by
 decide +kernel
def pointBounds75572 : List (Nat × Nat × Nat) := [(9909409792,116751737653870,116752127717141)]
theorem point_links_checked75572 : (cuts75572.take 1).map (fun c => (9909305345-1+2*2^10*c.k,116751608922599+c.lower,116751998985789+c.upper)) = pointBounds75572 := by
 decide +kernel
def cuts75573 : List PrefixCut := [⟨64,162445604,162445700⟩]
theorem checked75573 : checkPrefixCuts (2^48) 9909436417 10 Manual.Count131072.C075573.packed 64 cuts75573 = true := by
 decide +kernel
def cuts75574 : List PrefixCut := [⟨64,160682390,160682486⟩]
theorem checked75574 : checkPrefixCuts (2^48) 9909567489 10 Manual.Count131072.C075574.packed 64 cuts75574 = true := by
 decide +kernel
def cuts75575 : List PrefixCut := [⟨11,27068963,27068980⟩,
⟨64,160879085,160879182⟩]
theorem checked75575 : checkPrefixCuts (2^48) 9909698561 10 Manual.Count131072.C075575.packed 64 cuts75575 = true := by
 decide +kernel
def pointBounds75575 : List (Nat × Nat × Nat) := [(9909721088,116752120232265,116752510295763)]
theorem point_links_checked75575 : (cuts75575.take 1).map (fun c => (9909698561-1+2*2^10*c.k,116752093163302+c.lower,116752483226783+c.upper)) = pointBounds75575 := by
 decide +kernel
def cuts75576 : List PrefixCut := [⟨64,160876950,160877048⟩]
theorem checked75576 : checkPrefixCuts (2^48) 9909829633 10 Manual.Count131072.C075576.packed 64 cuts75576 = true := by
 decide +kernel
def cuts75577 : List PrefixCut := [⟨35,88816581,88816635⟩,
⟨64,161982552,161982652⟩]
theorem checked75577 : checkPrefixCuts (2^48) 9909960705 10 Manual.Count131072.C075577.packed 64 cuts75577 = true := by
 decide +kernel
def pointBounds75577 : List (Nat × Nat × Nat) := [(9910032384,116752503735918,116752893799648)]
theorem point_links_checked75577 : (cuts75577.take 1).map (fun c => (9909960705-1+2*2^10*c.k,116752414919337+c.lower,116752804983013+c.upper)) = pointBounds75577 := by
 decide +kernel
def cuts75578 : List PrefixCut := [⟨64,159963824,159963925⟩]
theorem checked75578 : checkPrefixCuts (2^48) 9910091777 10 Manual.Count131072.C075578.packed 64 cuts75578 = true := by
 decide +kernel
def cuts75579 : List PrefixCut := [⟨59,148828069,148828165⟩,
⟨64,161239794,161239898⟩]
theorem checked75579 : checkPrefixCuts (2^48) 9910222849 10 Manual.Count131072.C075579.packed 64 cuts75579 = true := by
 decide +kernel
def pointBounds75579 : List (Nat × Nat × Nat) := [(9910343680,116752885693782,116753275757755)]
theorem point_links_checked75579 : (cuts75579.take 1).map (fun c => (9910222849-1+2*2^10*c.k,116752736865713+c.lower,116753126929590+c.upper)) = pointBounds75579 := by
 decide +kernel
def cuts75580 : List PrefixCut := [⟨64,160698037,160698139⟩]
theorem checked75580 : checkPrefixCuts (2^48) 9910353921 10 Manual.Count131072.C075580.packed 64 cuts75580 = true := by
 decide +kernel
def cuts75581 : List PrefixCut := [⟨64,160979927,160980025⟩]
theorem checked75581 : checkPrefixCuts (2^48) 9910484993 10 Manual.Count131072.C075581.packed 64 cuts75581 = true := by
 decide +kernel
def cuts75582 : List PrefixCut := [⟨19,46748535,46748561⟩,
⟨64,160466577,160466673⟩]
theorem checked75582 : checkPrefixCuts (2^48) 9910616065 10 Manual.Count131072.C075582.packed 64 cuts75582 = true := by
 decide +kernel
def pointBounds75582 : List (Nat × Nat × Nat) := [(9910654976,116753266532006,116753656596213)]
theorem point_links_checked75582 : (cuts75582.take 1).map (fun c => (9910616065-1+2*2^10*c.k,116753219783471+c.lower,116753609847652+c.upper)) = pointBounds75582 := by
 decide +kernel
def cuts75583 : List PrefixCut := [⟨64,161657291,161657384⟩]
theorem checked75583 : checkPrefixCuts (2^48) 9910747137 10 Manual.Count131072.C075583.packed 64 cuts75583 = true := by
 decide +kernel
def cuts75584 : List PrefixCut := [⟨43,109938236,109938299⟩,
⟨64,163671580,163671675⟩]
theorem checked75584 : checkPrefixCuts (2^48) 9910878209 10 Manual.Count131072.C075584.packed 64 cuts75584 = true := by
 decide +kernel
def pointBounds75584 : List (Nat × Nat × Nat) := [(9910966272,116753651845575,116754041910008)]
theorem point_links_checked75584 : (cuts75584.take 1).map (fun c => (9910878209-1+2*2^10*c.k,116753541907339+c.lower,116753931971709+c.upper)) = pointBounds75584 := by
 decide +kernel
def cuts75585 : List PrefixCut := [⟨64,161227020,161227109⟩]
theorem checked75585 : checkPrefixCuts (2^48) 9911009281 10 Manual.Count131072.C075585.packed 64 cuts75585 = true := by
 decide +kernel
def cuts75586 : List PrefixCut := [⟨64,161366876,161366975⟩]
theorem checked75586 : checkPrefixCuts (2^48) 9911140353 10 Manual.Count131072.C075586.packed 64 cuts75586 = true := by
 decide +kernel
def cuts75587 : List PrefixCut := [⟨3,7469059,7469064⟩,
⟨64,160512762,160512854⟩]
theorem checked75587 : checkPrefixCuts (2^48) 9911271425 10 Manual.Count131072.C075587.packed 64 cuts75587 = true := by
 decide +kernel
def pointBounds75587 : List (Nat × Nat × Nat) := [(9911277568,116754035641874,116754425706532)]
theorem point_links_checked75587 : (cuts75587.take 1).map (fun c => (9911271425-1+2*2^10*c.k,116754028172815+c.lower,116754418237468+c.upper)) = pointBounds75587 := by
 decide +kernel
def cuts75588 : List PrefixCut := [⟨64,161192222,161192320⟩]
theorem checked75588 : checkPrefixCuts (2^48) 9911402497 10 Manual.Count131072.C075588.packed 64 cuts75588 = true := by
 decide +kernel
def cuts75589 : List PrefixCut := [⟨27,68071547,68071584⟩,
⟨64,160366523,160366615⟩]
theorem checked75589 : checkPrefixCuts (2^48) 9911533569 10 Manual.Count131072.C075589.packed 64 cuts75589 = true := by
 decide +kernel
def pointBounds75589 : List (Nat × Nat × Nat) := [(9911588864,116754417949346,116754808014226)]
theorem point_links_checked75589 : (cuts75589.take 1).map (fun c => (9911533569-1+2*2^10*c.k,116754349877799+c.lower,116754739942642+c.upper)) = pointBounds75589 := by
 decide +kernel
def cuts75590 : List PrefixCut := [⟨64,163175827,163175920⟩]
theorem checked75590 : checkPrefixCuts (2^48) 9911664641 10 Manual.Count131072.C075590.packed 64 cuts75590 = true := by
 decide +kernel
def cuts75591 : List PrefixCut := [⟨51,127818599,127818676⟩,
⟨64,160703058,160703155⟩]
theorem checked75591 : checkPrefixCuts (2^48) 9911795713 10 Manual.Count131072.C075591.packed 64 cuts75591 = true := by
 decide +kernel
def pointBounds75591 : List (Nat × Nat × Nat) := [(9911900160,116754801238748,116755191303853)]
theorem point_links_checked75591 : (cuts75591.take 1).map (fun c => (9911795713-1+2*2^10*c.k,116754673420149+c.lower,116755063485177+c.upper)) = pointBounds75591 := by
 decide +kernel
def cuts75592 : List PrefixCut := [⟨64,162262795,162262887⟩]
theorem checked75592 : checkPrefixCuts (2^48) 9911926785 10 Manual.Count131072.C075592.packed 64 cuts75592 = true := by
 decide +kernel
def cuts75593 : List PrefixCut := [⟨64,161550725,161550821⟩]
theorem checked75593 : checkPrefixCuts (2^48) 9912057857 10 Manual.Count131072.C075593.packed 64 cuts75593 = true := by
 decide +kernel
def cuts75594 : List PrefixCut := [⟨11,28396813,28396830⟩,
⟨64,160895465,160895567⟩]
theorem checked75594 : checkPrefixCuts (2^48) 9912188929 10 Manual.Count131072.C075594.packed 64 cuts75594 = true := by
 decide +kernel
def pointBounds75594 : List (Nat × Nat × Nat) := [(9912211456,116755186333540,116755576398870)]
theorem point_links_checked75594 : (cuts75594.take 1).map (fun c => (9912188929-1+2*2^10*c.k,116755157936727+c.lower,116755548002040+c.upper)) = pointBounds75594 := by
 decide +kernel
def cuts75595 : List PrefixCut := [⟨64,162398332,162398427⟩]
theorem checked75595 : checkPrefixCuts (2^48) 9912320001 10 Manual.Count131072.C075595.packed 64 cuts75595 = true := by
 decide +kernel
def cuts75596 : List PrefixCut := [⟨35,89220204,89220258⟩,
⟨64,162623353,162623454⟩]
theorem checked75596 : checkPrefixCuts (2^48) 9912451073 10 Manual.Count131072.C075596.packed 64 cuts75596 = true := by
 decide +kernel
def pointBounds75596 : List (Nat × Nat × Nat) := [(9912522752,116755570450728,116755960516292)]
theorem point_links_checked75596 : (cuts75596.take 1).map (fun c => (9912451073-1+2*2^10*c.k,116755481230524+c.lower,116755871296034+c.upper)) = pointBounds75596 := by
 decide +kernel
def cuts75597 : List PrefixCut := [⟨64,161769335,161769427⟩]
theorem checked75597 : checkPrefixCuts (2^48) 9912582145 10 Manual.Count131072.C075597.packed 64 cuts75597 = true := by
 decide +kernel
def cuts75598 : List PrefixCut := [⟨59,149415387,149415478⟩,
⟨64,161767205,161767302⟩]
theorem checked75598 : checkPrefixCuts (2^48) 9912713217 10 Manual.Count131072.C075598.packed 64 cuts75598 = true := by
 decide +kernel
def pointBounds75598 : List (Nat × Nat × Nat) := [(9912834048,116755955038599,116756345104393)]
theorem point_links_checked75598 : (cuts75598.take 1).map (fun c => (9912713217-1+2*2^10*c.k,116755805623212+c.lower,116756195688915+c.upper)) = pointBounds75598 := by
 decide +kernel
def cuts75599 : List PrefixCut := [⟨64,162304570,162304666⟩]
theorem checked75599 : checkPrefixCuts (2^48) 9912844289 10 Manual.Count131072.C075599.packed 64 cuts75599 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000174
