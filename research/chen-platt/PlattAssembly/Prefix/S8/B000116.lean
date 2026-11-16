import PlattAssemblyKernel
import PlattCertificates.Count131072.C073712
import PlattCertificates.Count131072.C073713
import PlattCertificates.Count131072.C073714
import PlattCertificates.Count131072.C073715
import PlattCertificates.Count131072.C073716
import PlattCertificates.Count131072.C073717
import PlattCertificates.Count131072.C073718
import PlattCertificates.Count131072.C073719
import PlattCertificates.Count131072.C073720
import PlattCertificates.Count131072.C073721
import PlattCertificates.Count131072.C073722
import PlattCertificates.Count131072.C073723
import PlattCertificates.Count131072.C073724
import PlattCertificates.Count131072.C073725
import PlattCertificates.Count131072.C073726
import PlattCertificates.Count131072.C073727
import PlattCertificates.Count131072.C073728
import PlattCertificates.Count131072.C073729
import PlattCertificates.Count131072.C073730
import PlattCertificates.Count131072.C073731
import PlattCertificates.Count131072.C073732
import PlattCertificates.Count131072.C073733
import PlattCertificates.Count131072.C073734
import PlattCertificates.Count131072.C073735
import PlattCertificates.Count131072.C073736
import PlattCertificates.Count131072.C073737
import PlattCertificates.Count131072.C073738
import PlattCertificates.Count131072.C073739
import PlattCertificates.Count131072.C073740
import PlattCertificates.Count131072.C073741
import PlattCertificates.Count131072.C073742
import PlattCertificates.Count131072.C073743
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000116
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts73712 : List PrefixCut := [⟨64,165322042,165322146⟩]
theorem checked73712 : checkPrefixCuts (2^48) 9665511425 10 Manual.Count131072.C073712.packed 64 cuts73712 = true := by
 decide +kernel
def cuts73713 : List PrefixCut := [⟨64,163543434,163543535⟩]
theorem checked73713 : checkPrefixCuts (2^48) 9665642497 10 Manual.Count131072.C073713.packed 64 cuts73713 = true := by
 decide +kernel
def cuts73714 : List PrefixCut := [⟨2,5067015,5067018⟩,
⟨64,169044998,169045096⟩]
theorem checked73714 : checkPrefixCuts (2^48) 9665773569 10 Manual.Count131072.C073714.packed 64 cuts73714 = true := by
 decide +kernel
def pointBounds73714 : List (Nat × Nat × Nat) := [(9665777664,116447129827828,116447519708638)]
theorem point_links_checked73714 : (cuts73714.take 1).map (fun c => (9665773569-1+2*2^10*c.k,116447124760813+c.lower,116447514641620+c.upper)) = pointBounds73714 := by
 decide +kernel
def cuts73715 : List PrefixCut := [⟨64,164994997,164995091⟩]
theorem checked73715 : checkPrefixCuts (2^48) 9665904641 10 Manual.Count131072.C073715.packed 64 cuts73715 = true := by
 decide +kernel
def cuts73716 : List PrefixCut := [⟨22,56143217,56143250⟩,
⟨64,165662507,165662606⟩]
theorem checked73716 : checkPrefixCuts (2^48) 9666035713 10 Manual.Count131072.C073716.packed 64 cuts73716 = true := by
 decide +kernel
def pointBounds73716 : List (Nat × Nat × Nat) := [(9666080768,116447514944025,116447904825057)]
theorem point_links_checked73716 : (cuts73716.take 1).map (fun c => (9666035713-1+2*2^10*c.k,116447458800808+c.lower,116447848681807+c.upper)) = pointBounds73716 := by
 decide +kernel
def cuts73717 : List PrefixCut := [⟨64,165252597,165252693⟩]
theorem checked73717 : checkPrefixCuts (2^48) 9666166785 10 Manual.Count131072.C073717.packed 64 cuts73717 = true := by
 decide +kernel
def cuts73718 : List PrefixCut := [⟨42,106721406,106721470⟩,
⟨64,164347664,164347760⟩]
theorem checked73718 : checkPrefixCuts (2^48) 9666297857 10 Manual.Count131072.C073718.packed 64 cuts73718 = true := by
 decide +kernel
def pointBounds73718 : List (Nat × Nat × Nat) := [(9666383872,116447896437318,116448286318576)]
theorem point_links_checked73718 : (cuts73718.take 1).map (fun c => (9666297857-1+2*2^10*c.k,116447789715912+c.lower,116448179597106+c.upper)) = pointBounds73718 := by
 decide +kernel
def cuts73719 : List PrefixCut := [⟨64,165393700,165393801⟩]
theorem checked73719 : checkPrefixCuts (2^48) 9666428929 10 Manual.Count131072.C073719.packed 64 cuts73719 = true := by
 decide +kernel
def cuts73720 : List PrefixCut := [⟨62,160208456,160208549⟩,
⟨64,165537055,165537151⟩]
theorem checked73720 : checkPrefixCuts (2^48) 9666560001 10 Manual.Count131072.C073720.packed 64 cuts73720 = true := by
 decide +kernel
def pointBounds73720 : List (Nat × Nat × Nat) := [(9666686976,116448279665732,116448669547216)]
theorem point_links_checked73720 : (cuts73720.take 1).map (fun c => (9666560001-1+2*2^10*c.k,116448119457276+c.lower,116448509338667+c.upper)) = pointBounds73720 := by
 decide +kernel
def cuts73721 : List PrefixCut := [⟨64,168097190,168097291⟩]
theorem checked73721 : checkPrefixCuts (2^48) 9666691073 10 Manual.Count131072.C073721.packed 64 cuts73721 = true := by
 decide +kernel
def cuts73722 : List PrefixCut := [⟨64,167075792,167075892⟩]
theorem checked73722 : checkPrefixCuts (2^48) 9666822145 10 Manual.Count131072.C073722.packed 64 cuts73722 = true := by
 decide +kernel
def cuts73723 : List PrefixCut := [⟨18,47373641,47373668⟩,
⟨64,162705987,162706085⟩]
theorem checked73723 : checkPrefixCuts (2^48) 9666953217 10 Manual.Count131072.C073723.packed 64 cuts73723 = true := by
 decide +kernel
def pointBounds73723 : List (Nat × Nat × Nat) := [(9666990080,116448667540954,116449057422669)]
theorem point_links_checked73723 : (cuts73723.take 1).map (fun c => (9666953217-1+2*2^10*c.k,116448620167313+c.lower,116449010049001+c.upper)) = pointBounds73723 := by
 decide +kernel
def cuts73724 : List PrefixCut := [⟨64,170041166,170041260⟩]
theorem checked73724 : checkPrefixCuts (2^48) 9667084289 10 Manual.Count131072.C073724.packed 64 cuts73724 = true := by
 decide +kernel
def cuts73725 : List PrefixCut := [⟨38,101528615,101528677⟩,
⟨64,170708527,170708630⟩]
theorem checked73725 : checkPrefixCuts (2^48) 9667215361 10 Manual.Count131072.C073725.packed 64 cuts73725 = true := by
 decide +kernel
def pointBounds73725 : List (Nat × Nat × Nat) := [(9667293184,116449054443081,116449444325023)]
theorem point_links_checked73725 : (cuts73725.take 1).map (fun c => (9667215361-1+2*2^10*c.k,116448952914466+c.lower,116449342796346+c.upper)) = pointBounds73725 := by
 decide +kernel
def cuts73726 : List PrefixCut := [⟨64,167124955,167125057⟩]
theorem checked73726 : checkPrefixCuts (2^48) 9667346433 10 Manual.Count131072.C073726.packed 64 cuts73726 = true := by
 decide +kernel
def cuts73727 : List PrefixCut := [⟨58,149042087,149042185⟩,
⟨64,163687070,163687176⟩]
theorem checked73727 : checkPrefixCuts (2^48) 9667477505 10 Manual.Count131072.C073727.packed 64 cuts73727 = true := by
 decide +kernel
def pointBounds73727 : List (Nat × Nat × Nat) := [(9667596288,116449439790035,116449829672218)]
theorem point_links_checked73727 : (cuts73727.take 1).map (fun c => (9667477505-1+2*2^10*c.k,116449290747948+c.lower,116449680630033+c.upper)) = pointBounds73727 := by
 decide +kernel
def cuts73728 : List PrefixCut := [⟨64,164121576,164121672⟩]
theorem checked73728 : checkPrefixCuts (2^48) 9667608577 10 Manual.Count131072.C073728.packed 64 cuts73728 = true := by
 decide +kernel
def cuts73729 : List PrefixCut := [⟨64,167671355,167671451⟩]
theorem checked73729 : checkPrefixCuts (2^48) 9667739649 10 Manual.Count131072.C073729.packed 64 cuts73729 = true := by
 decide +kernel
def cuts73730 : List PrefixCut := [⟨14,36218342,36218364⟩,
⟨64,166504502,166504602⟩]
theorem checked73730 : checkPrefixCuts (2^48) 9667870721 10 Manual.Count131072.C073730.packed 64 cuts73730 = true := by
 decide +kernel
def pointBounds73730 : List (Nat × Nat × Nat) := [(9667899392,116449822446291,116450212328696)]
theorem point_links_checked73730 : (cuts73730.take 1).map (fun c => (9667870721-1+2*2^10*c.k,116449786227949+c.lower,116450176110332+c.upper)) = pointBounds73730 := by
 decide +kernel
def cuts73731 : List PrefixCut := [⟨64,168219957,168220058⟩]
theorem checked73731 : checkPrefixCuts (2^48) 9668001793 10 Manual.Count131072.C073731.packed 64 cuts73731 = true := by
 decide +kernel
def cuts73732 : List PrefixCut := [⟨34,88476143,88476198⟩,
⟨64,165218995,165219096⟩]
theorem checked73732 : checkPrefixCuts (2^48) 9668132865 10 Manual.Count131072.C073732.packed 64 cuts73732 = true := by
 decide +kernel
def pointBounds73732 : List (Nat × Nat × Nat) := [(9668202496,116450209428551,116450599311190)]
theorem point_links_checked73732 : (cuts73732.take 1).map (fun c => (9668132865-1+2*2^10*c.k,116450120952408+c.lower,116450510834992+c.upper)) = pointBounds73732 := by
 decide +kernel
def cuts73733 : List PrefixCut := [⟨64,165857243,165857346⟩]
theorem checked73733 : checkPrefixCuts (2^48) 9668263937 10 Manual.Count131072.C073733.packed 64 cuts73733 = true := by
 decide +kernel
def cuts73734 : List PrefixCut := [⟨54,139275256,139275342⟩,
⟨64,165476527,165476629⟩]
theorem checked73734 : checkPrefixCuts (2^48) 9668395009 10 Manual.Count131072.C073734.packed 64 cuts73734 = true := by
 decide +kernel
def pointBounds73734 : List (Nat × Nat × Nat) := [(9668505600,116450591303902,116450981186776)]
theorem point_links_checked73734 : (cuts73734.take 1).map (fun c => (9668395009-1+2*2^10*c.k,116450452028646+c.lower,116450841911434+c.upper)) = pointBounds73734 := by
 decide +kernel
def cuts73735 : List PrefixCut := [⟨64,165794514,165794611⟩]
theorem checked73735 : checkPrefixCuts (2^48) 9668526081 10 Manual.Count131072.C073735.packed 64 cuts73735 = true := by
 decide +kernel
def cuts73736 : List PrefixCut := [⟨64,168819899,168820004⟩]
theorem checked73736 : checkPrefixCuts (2^48) 9668657153 10 Manual.Count131072.C073736.packed 64 cuts73736 = true := by
 decide +kernel
def cuts73737 : List PrefixCut := [⟨10,24861368,24861383⟩,
⟨64,164130664,164130769⟩]
theorem checked73737 : checkPrefixCuts (2^48) 9668788225 10 Manual.Count131072.C073737.packed 64 cuts73737 = true := by
 decide +kernel
def pointBounds73737 : List (Nat × Nat × Nat) := [(9668808704,116450976980954,116451366864061)]
theorem point_links_checked73737 : (cuts73737.take 1).map (fun c => (9668788225-1+2*2^10*c.k,116450952119586+c.lower,116451342002678+c.upper)) = pointBounds73737 := by
 decide +kernel
def cuts73738 : List PrefixCut := [⟨64,165816882,165816980⟩]
theorem checked73738 : checkPrefixCuts (2^48) 9668919297 10 Manual.Count131072.C073738.packed 64 cuts73738 = true := by
 decide +kernel
def cuts73739 : List PrefixCut := [⟨30,75135029,75135081⟩,
⟨64,162583337,162583443⟩]
theorem checked73739 : checkPrefixCuts (2^48) 9669050369 10 Manual.Count131072.C073739.packed 64 cuts73739 = true := by
 decide +kernel
def pointBounds73739 : List (Nat × Nat × Nat) := [(9669111808,116451357202161,116451747085508)]
theorem point_links_checked73739 : (cuts73739.take 1).map (fun c => (9669050369-1+2*2^10*c.k,116451282067132+c.lower,116451671950427+c.upper)) = pointBounds73739 := by
 decide +kernel
def cuts73740 : List PrefixCut := [⟨64,167180576,167180681⟩]
theorem checked73740 : checkPrefixCuts (2^48) 9669181441 10 Manual.Count131072.C073740.packed 64 cuts73740 = true := by
 decide +kernel
def cuts73741 : List PrefixCut := [⟨50,128986274,128986355⟩,
⟨64,165693699,165693803⟩]
theorem checked73741 : checkPrefixCuts (2^48) 9669312513 10 Manual.Count131072.C073741.packed 64 cuts73741 = true := by
 decide +kernel
def pointBounds73741 : List (Nat × Nat × Nat) := [(9669414912,116451740817319,116452130700906)]
theorem point_links_checked73741 : (cuts73741.take 1).map (fun c => (9669312513-1+2*2^10*c.k,116451611831045+c.lower,116452001714551+c.upper)) = pointBounds73741 := by
 decide +kernel
def cuts73742 : List PrefixCut := [⟨64,165371254,165371348⟩]
theorem checked73742 : checkPrefixCuts (2^48) 9669443585 10 Manual.Count131072.C073742.packed 64 cuts73742 = true := by
 decide +kernel
def cuts73743 : List PrefixCut := [⟨64,166504271,166504375⟩]
theorem checked73743 : checkPrefixCuts (2^48) 9669574657 10 Manual.Count131072.C073743.packed 64 cuts73743 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000116
