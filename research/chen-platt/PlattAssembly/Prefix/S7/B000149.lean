import PlattAssemblyKernel
import PlattCertificates.Count131072.C064768
import PlattCertificates.Count131072.C064769
import PlattCertificates.Count131072.C064770
import PlattCertificates.Count131072.C064771
import PlattCertificates.Count131072.C064772
import PlattCertificates.Count131072.C064773
import PlattCertificates.Count131072.C064774
import PlattCertificates.Count131072.C064775
import PlattCertificates.Count131072.C064776
import PlattCertificates.Count131072.C064777
import PlattCertificates.Count131072.C064778
import PlattCertificates.Count131072.C064779
import PlattCertificates.Count131072.C064780
import PlattCertificates.Count131072.C064781
import PlattCertificates.Count131072.C064782
import PlattCertificates.Count131072.C064783
import PlattCertificates.Count131072.C064784
import PlattCertificates.Count131072.C064785
import PlattCertificates.Count131072.C064786
import PlattCertificates.Count131072.C064787
import PlattCertificates.Count131072.C064788
import PlattCertificates.Count131072.C064789
import PlattCertificates.Count131072.C064790
import PlattCertificates.Count131072.C064791
import PlattCertificates.Count131072.C064792
import PlattCertificates.Count131072.C064793
import PlattCertificates.Count131072.C064794
import PlattCertificates.Count131072.C064795
import PlattCertificates.Count131072.C064796
import PlattCertificates.Count131072.C064797
import PlattCertificates.Count131072.C064798
import PlattCertificates.Count131072.C064799
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000149
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts64768 : List PrefixCut := [⟨64,191190069,191190173⟩]
theorem checked64768 : checkPrefixCuts (2^48) 8493203457 10 Manual.Count131072.C064768.packed 64 cuts64768 = true := by
 decide +kernel
def cuts64769 : List PrefixCut := [⟨14,40000734,40000761⟩,
⟨64,187243398,187243509⟩]
theorem checked64769 : checkPrefixCuts (2^48) 8493334529 10 Manual.Count131072.C064769.packed 64 cuts64769 = true := by
 decide +kernel
def pointBounds64769 : List (Nat × Nat × Nat) := [(8493363200,114859639316720,114860028265416)]
theorem point_links_checked64769 : (cuts64769.take 1).map (fun c => (8493334529-1+2*2^10*c.k,114859599315986+c.lower,114859988264655+c.upper)) = pointBounds64769 := by
 decide +kernel
def cuts64770 : List PrefixCut := [⟨64,189991138,189991247⟩]
theorem checked64770 : checkPrefixCuts (2^48) 8493465601 10 Manual.Count131072.C064770.packed 64 cuts64770 = true := by
 decide +kernel
def cuts64771 : List PrefixCut := [⟨16,46991947,46991972⟩,
⟨64,189756231,189756339⟩]
theorem checked64771 : checkPrefixCuts (2^48) 8493596673 10 Manual.Count131072.C064771.packed 64 cuts64771 = true := by
 decide +kernel
def pointBounds64771 : List (Nat × Nat × Nat) := [(8493629440,114860023542469,114860412491383)]
theorem point_links_checked64771 : (cuts64771.take 1).map (fun c => (8493596673-1+2*2^10*c.k,114859976550522+c.lower,114860365499411+c.upper)) = pointBounds64771 := by
 decide +kernel
def cuts64772 : List PrefixCut := [⟨64,188792263,188792366⟩]
theorem checked64772 : checkPrefixCuts (2^48) 8493727745 10 Manual.Count131072.C064772.packed 64 cuts64772 = true := by
 decide +kernel
def cuts64773 : List PrefixCut := [⟨18,53684473,53684504⟩,
⟨64,188491113,188491222⟩]
theorem checked64773 : checkPrefixCuts (2^48) 8493858817 10 Manual.Count131072.C064773.packed 64 cuts64773 = true := by
 decide +kernel
def pointBounds64773 : List (Nat × Nat × Nat) := [(8493895680,114860408783489,114860797732620)]
theorem point_links_checked64773 : (cuts64773.take 1).map (fun c => (8493858817-1+2*2^10*c.k,114860355099016+c.lower,114860744048116+c.upper)) = pointBounds64773 := by
 decide +kernel
def cuts64774 : List PrefixCut := [⟨64,189681163,189681277⟩]
theorem checked64774 : checkPrefixCuts (2^48) 8493989889 10 Manual.Count131072.C064774.packed 64 cuts64774 = true := by
 decide +kernel
def cuts64775 : List PrefixCut := [⟨20,59183634,59183672⟩,
⟨64,189379998,189380112⟩]
theorem checked64775 : checkPrefixCuts (2^48) 8494120961 10 Manual.Count131072.C064775.packed 64 cuts64775 = true := by
 decide +kernel
def pointBounds64775 : List (Nat × Nat × Nat) := [(8494161920,114860792454926,114861181404287)]
theorem point_links_checked64775 : (cuts64775.take 1).map (fun c => (8494120961-1+2*2^10*c.k,114860733271292+c.lower,114861122220615+c.upper)) = pointBounds64775 := by
 decide +kernel
def cuts64776 : List PrefixCut := [⟨64,191398416,191398527⟩]
theorem checked64776 : checkPrefixCuts (2^48) 8494252033 10 Manual.Count131072.C064776.packed 64 cuts64776 = true := by
 decide +kernel
def cuts64777 : List PrefixCut := [⟨22,66869459,66869501⟩,
⟨64,191759973,191760093⟩]
theorem checked64777 : checkPrefixCuts (2^48) 8494383105 10 Manual.Count131072.C064777.packed 64 cuts64777 = true := by
 decide +kernel
def pointBounds64777 : List (Nat × Nat × Nat) := [(8494428160,114861180919165,114861569868755)]
theorem point_links_checked64777 : (cuts64777.take 1).map (fun c => (8494383105-1+2*2^10*c.k,114861114049706+c.lower,114861502999254+c.upper)) = pointBounds64777 := by
 decide +kernel
def cuts64778 : List PrefixCut := [⟨64,188542854,188542971⟩]
theorem checked64778 : checkPrefixCuts (2^48) 8494514177 10 Manual.Count131072.C064778.packed 64 cuts64778 = true := by
 decide +kernel
def cuts64779 : List PrefixCut := [⟨24,70313471,70313516⟩,
⟨64,189235762,189235877⟩]
theorem checked64779 : checkPrefixCuts (2^48) 8494645249 10 Manual.Count131072.C064779.packed 64 cuts64779 = true := by
 decide +kernel
def pointBounds64779 : List (Nat × Nat × Nat) := [(8494694400,114861564666004,114861953615834)]
theorem point_links_checked64779 : (cuts64779.take 1).map (fun c => (8494645249-1+2*2^10*c.k,114861494352533+c.lower,114861883302318+c.upper)) = pointBounds64779 := by
 decide +kernel
def cuts64780 : List PrefixCut := [⟨64,188570158,188570264⟩]
theorem checked64780 : checkPrefixCuts (2^48) 8494776321 10 Manual.Count131072.C064780.packed 64 cuts64780 = true := by
 decide +kernel
def cuts64781 : List PrefixCut := [⟨26,77435190,77435236⟩,
⟨64,191151717,191151824⟩]
theorem checked64781 : checkPrefixCuts (2^48) 8494907393 10 Manual.Count131072.C064781.packed 64 cuts64781 = true := by
 decide +kernel
def pointBounds64781 : List (Nat × Nat × Nat) := [(8494960640,114861949593643,114862338543695)]
theorem point_links_checked64781 : (cuts64781.take 1).map (fun c => (8494907393-1+2*2^10*c.k,114861872158453+c.lower,114862261108459+c.upper)) = pointBounds64781 := by
 decide +kernel
def cuts64782 : List PrefixCut := [⟨64,188696868,188696973⟩]
theorem checked64782 : checkPrefixCuts (2^48) 8495038465 10 Manual.Count131072.C064782.packed 64 cuts64782 = true := by
 decide +kernel
def cuts64783 : List PrefixCut := [⟨28,83529328,83529379⟩,
⟨64,190284353,190284465⟩]
theorem checked64783 : checkPrefixCuts (2^48) 8495169537 10 Manual.Count131072.C064783.packed 64 cuts64783 = true := by
 decide +kernel
def pointBounds64783 : List (Nat × Nat × Nat) := [(8495226880,114862335536366,114862724486635)]
theorem point_links_checked64783 : (cuts64783.take 1).map (fun c => (8495169537-1+2*2^10*c.k,114862252007038+c.lower,114862640957256+c.upper)) = pointBounds64783 := by
 decide +kernel
def cuts64784 : List PrefixCut := [⟨64,192700101,192700215⟩]
theorem checked64784 : checkPrefixCuts (2^48) 8495300609 10 Manual.Count131072.C064784.packed 64 cuts64784 = true := by
 decide +kernel
def cuts64785 : List PrefixCut := [⟨30,91180317,91180368⟩,
⟨64,190974274,190974384⟩]
theorem checked64785 : checkPrefixCuts (2^48) 8495431681 10 Manual.Count131072.C064785.packed 64 cuts64785 = true := by
 decide +kernel
def pointBounds64785 : List (Nat × Nat × Nat) := [(8495493120,114862726171809,114863115122304)]
theorem point_links_checked64785 : (cuts64785.take 1).map (fun c => (8495431681-1+2*2^10*c.k,114862634991492+c.lower,114863023941936+c.upper)) = pointBounds64785 := by
 decide +kernel
def cuts64786 : List PrefixCut := [⟨64,192164068,192164176⟩]
theorem checked64786 : checkPrefixCuts (2^48) 8495562753 10 Manual.Count131072.C064786.packed 64 cuts64786 = true := by
 decide +kernel
def cuts64787 : List PrefixCut := [⟨32,95318896,95318952⟩,
⟨64,190040695,190040810⟩]
theorem checked64787 : checkPrefixCuts (2^48) 8495693825 10 Manual.Count131072.C064787.packed 64 cuts64787 = true := by
 decide +kernel
def pointBounds64787 : List (Nat × Nat × Nat) := [(8495759360,114863113448730,114863502399448)]
theorem point_links_checked64787 : (cuts64787.take 1).map (fun c => (8495693825-1+2*2^10*c.k,114863018129834+c.lower,114863407080496+c.upper)) = pointBounds64787 := by
 decide +kernel
def cuts64788 : List PrefixCut := [⟨64,192390042,192390149⟩]
theorem checked64788 : checkPrefixCuts (2^48) 8495824897 10 Manual.Count131072.C064788.packed 64 cuts64788 = true := by
 decide +kernel
def cuts64789 : List PrefixCut := [⟨34,100020436,100020492⟩,
⟨64,190763686,190763790⟩]
theorem checked64789 : checkPrefixCuts (2^48) 8495955969 10 Manual.Count131072.C064789.packed 64 cuts64789 = true := by
 decide +kernel
def pointBounds64789 : List (Nat × Nat × Nat) := [(8496025600,114863500581007,114863889531947)]
theorem point_links_checked64789 : (cuts64789.take 1).map (fun c => (8495955969-1+2*2^10*c.k,114863400560571+c.lower,114863789511455+c.upper)) = pointBounds64789 := by
 decide +kernel
def cuts64790 : List PrefixCut := [⟨64,185990064,185990177⟩]
theorem checked64790 : checkPrefixCuts (2^48) 8496087041 10 Manual.Count131072.C064790.packed 64 cuts64790 = true := by
 decide +kernel
def cuts64791 : List PrefixCut := [⟨36,106245629,106245692⟩,
⟨64,187444891,187445003⟩]
theorem checked64791 : checkPrefixCuts (2^48) 8496218113 10 Manual.Count131072.C064791.packed 64 cuts64791 = true := by
 decide +kernel
def pointBounds64791 : List (Nat × Nat × Nat) := [(8496291840,114863883559950,114864272511114)]
theorem point_links_checked64791 : (cuts64791.take 1).map (fun c => (8496218113-1+2*2^10*c.k,114863777314321+c.lower,114864166265422+c.upper)) = pointBounds64791 := by
 decide +kernel
def cuts64792 : List PrefixCut := [⟨64,189661638,189661746⟩]
theorem checked64792 : checkPrefixCuts (2^48) 8496349185 10 Manual.Count131072.C064792.packed 64 cuts64792 = true := by
 decide +kernel
def cuts64793 : List PrefixCut := [⟨38,113099881,113099949⟩,
⟨64,188432962,188433074⟩]
theorem checked64793 : checkPrefixCuts (2^48) 8496480257 10 Manual.Count131072.C064793.packed 64 cuts64793 = true := by
 decide +kernel
def pointBounds64793 : List (Nat × Nat × Nat) := [(8496558080,114864267520731,114864656472120)]
theorem point_links_checked64793 : (cuts64793.take 1).map (fun c => (8496480257-1+2*2^10*c.k,114864154420850+c.lower,114864543372171+c.upper)) = pointBounds64793 := by
 decide +kernel
def cuts64794 : List PrefixCut := [⟨64,188794446,188794558⟩]
theorem checked64794 : checkPrefixCuts (2^48) 8496611329 10 Manual.Count131072.C064794.packed 64 cuts64794 = true := by
 decide +kernel
def cuts64795 : List PrefixCut := [⟨40,121311917,121311990⟩,
⟨64,192269900,192270014⟩]
theorem checked64795 : checkPrefixCuts (2^48) 8496742401 10 Manual.Count131072.C064795.packed 64 cuts64795 = true := by
 decide +kernel
def pointBounds64795 : List (Nat × Nat × Nat) := [(8496824320,114864652960175,114865041911793)]
theorem point_links_checked64795 : (cuts64795.take 1).map (fun c => (8496742401-1+2*2^10*c.k,114864531648258+c.lower,114864920599803+c.upper)) = pointBounds64795 := by
 decide +kernel
def cuts64796 : List PrefixCut := [⟨64,187264792,187264901⟩]
theorem checked64796 : checkPrefixCuts (2^48) 8496873473 10 Manual.Count131072.C064796.packed 64 cuts64796 = true := by
 decide +kernel
def cuts64797 : List PrefixCut := [⟨42,126144569,126144647⟩,
⟨64,191303300,191303416⟩]
theorem checked64797 : checkPrefixCuts (2^48) 8497004545 10 Manual.Count131072.C064797.packed 64 cuts64797 = true := by
 decide +kernel
def pointBounds64797 : List (Nat × Nat × Nat) := [(8497090560,114865037327519,114865426279365)]
theorem point_links_checked64797 : (cuts64797.take 1).map (fun c => (8497004545-1+2*2^10*c.k,114864911182950+c.lower,114865300134718+c.upper)) = pointBounds64797 := by
 decide +kernel
def cuts64798 : List PrefixCut := [⟨64,190969084,190969191⟩]
theorem checked64798 : checkPrefixCuts (2^48) 8497135617 10 Manual.Count131072.C064798.packed 64 cuts64798 = true := by
 decide +kernel
def cuts64799 : List PrefixCut := [⟨44,128923155,128923231⟩,
⟨64,188978625,188978736⟩]
theorem checked64799 : checkPrefixCuts (2^48) 8497266689 10 Manual.Count131072.C064799.packed 64 cuts64799 = true := by
 decide +kernel
def pointBounds64799 : List (Nat × Nat × Nat) := [(8497356800,114865422378489,114865811330556)]
theorem point_links_checked64799 : (cuts64799.take 1).map (fun c => (8497266689-1+2*2^10*c.k,114865293455334+c.lower,114865682407325+c.upper)) = pointBounds64799 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000149
