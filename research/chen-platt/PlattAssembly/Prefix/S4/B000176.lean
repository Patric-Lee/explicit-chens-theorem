import PlattAssemblyKernel
import PlattCertificates.Count131072.C035632
import PlattCertificates.Count131072.C035633
import PlattCertificates.Count131072.C035634
import PlattCertificates.Count131072.C035635
import PlattCertificates.Count131072.C035636
import PlattCertificates.Count131072.C035637
import PlattCertificates.Count131072.C035638
import PlattCertificates.Count131072.C035639
import PlattCertificates.Count131072.C035640
import PlattCertificates.Count131072.C035641
import PlattCertificates.Count131072.C035642
import PlattCertificates.Count131072.C035643
import PlattCertificates.Count131072.C035644
import PlattCertificates.Count131072.C035645
import PlattCertificates.Count131072.C035646
import PlattCertificates.Count131072.C035647
import PlattCertificates.Count131072.C035648
import PlattCertificates.Count131072.C035649
import PlattCertificates.Count131072.C035650
import PlattCertificates.Count131072.C035651
import PlattCertificates.Count131072.C035652
import PlattCertificates.Count131072.C035653
import PlattCertificates.Count131072.C035654
import PlattCertificates.Count131072.C035655
import PlattCertificates.Count131072.C035656
import PlattCertificates.Count131072.C035657
import PlattCertificates.Count131072.C035658
import PlattCertificates.Count131072.C035659
import PlattCertificates.Count131072.C035660
import PlattCertificates.Count131072.C035661
import PlattCertificates.Count131072.C035662
import PlattCertificates.Count131072.C035663
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000176
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts35632 : List PrefixCut := [⟨64,350160897,350161115⟩]
theorem checked35632 : checkPrefixCuts (2^48) 4674289665 10 Manual.Count131072.C035632.packed 64 cuts35632 = true := by
 decide +kernel
def cuts35633 : List PrefixCut := [⟨8,44017812,44017841⟩,
⟨64,355931741,355931963⟩]
theorem checked35633 : checkPrefixCuts (2^48) 4674420737 10 Manual.Count131072.C035633.packed 64 cuts35633 = true := by
 decide +kernel
def pointBounds35633 : List (Nat × Nat × Nat) := [(4674437120,107409731081877,107410115705100)]
theorem point_links_checked35633 : (cuts35633.take 1).map (fun c => (4674420737-1+2*2^10*c.k,107409687064065+c.lower,107410071687259+c.upper)) = pointBounds35633 := by
 decide +kernel
def cuts35634 : List PrefixCut := [⟨16,88213645,88213699⟩,
⟨64,353332546,353332767⟩]
theorem checked35634 : checkPrefixCuts (2^48) 4674551809 10 Manual.Count131072.C035634.packed 64 cuts35634 = true := by
 decide +kernel
def pointBounds35634 : List (Nat × Nat × Nat) := [(4674584576,107410131209451,107410515832921)]
theorem point_links_checked35634 : (cuts35634.take 1).map (fun c => (4674551809-1+2*2^10*c.k,107410042995806+c.lower,107410427619222+c.upper)) = pointBounds35634 := by
 decide +kernel
def cuts35635 : List PrefixCut := [⟨24,133189606,133189689⟩,
⟨64,354406483,354406704⟩]
theorem checked35635 : checkPrefixCuts (2^48) 4674682881 10 Manual.Count131072.C035635.packed 64 cuts35635 = true := by
 decide +kernel
def pointBounds35635 : List (Nat × Nat × Nat) := [(4674732032,107410529517958,107410914141678)]
theorem point_links_checked35635 : (cuts35635.take 1).map (fun c => (4674682881-1+2*2^10*c.k,107410396328352+c.lower,107410780951989+c.upper)) = pointBounds35635 := by
 decide +kernel
def cuts35636 : List PrefixCut := [⟨32,182136779,182136891⟩,
⟨64,357467332,357467554⟩]
theorem checked35636 : checkPrefixCuts (2^48) 4674813953 10 Manual.Count131072.C035636.packed 64 cuts35636 = true := by
 decide +kernel
def pointBounds35636 : List (Nat × Nat × Nat) := [(4674879488,107410932871614,107411317495584)]
theorem point_links_checked35636 : (cuts35636.take 1).map (fun c => (4674813953-1+2*2^10*c.k,107410750734835+c.lower,107411135358693+c.upper)) = pointBounds35636 := by
 decide +kernel
def cuts35637 : List PrefixCut := [⟨40,221929313,221929452⟩,
⟨64,351918104,351918322⟩]
theorem checked35637 : checkPrefixCuts (2^48) 4674945025 10 Manual.Count131072.C035637.packed 64 cuts35637 = true := by
 decide +kernel
def pointBounds35637 : List (Nat × Nat × Nat) := [(4675026944,107411330131480,107411714755699)]
theorem point_links_checked35637 : (cuts35637.take 1).map (fun c => (4674945025-1+2*2^10*c.k,107411108202167+c.lower,107411492826247+c.upper)) = pointBounds35637 := by
 decide +kernel
def cuts35638 : List PrefixCut := [⟨48,267860617,267860780⟩,
⟨64,353353242,353353460⟩]
theorem checked35638 : checkPrefixCuts (2^48) 4675076097 10 Manual.Count131072.C035638.packed 64 cuts35638 = true := by
 decide +kernel
def pointBounds35638 : List (Nat × Nat × Nat) := [(4675174400,107411727980888,107412112605349)]
theorem point_links_checked35638 : (cuts35638.take 1).map (fun c => (4675076097-1+2*2^10*c.k,107411460120271+c.lower,107411844744569+c.upper)) = pointBounds35638 := by
 decide +kernel
def cuts35639 : List PrefixCut := [⟨56,310839051,310839244⟩,
⟨64,355269813,355270035⟩]
theorem checked35639 : checkPrefixCuts (2^48) 4675207169 10 Manual.Count131072.C035639.packed 64 cuts35639 = true := by
 decide +kernel
def pointBounds35639 : List (Nat × Nat × Nat) := [(4675321856,107412124312564,107412508937273)]
theorem point_links_checked35639 : (cuts35639.take 1).map (fun c => (4675207169-1+2*2^10*c.k,107411813473513+c.lower,107412198098029+c.upper)) = pointBounds35639 := by
 decide +kernel
def cuts35640 : List PrefixCut := [⟨64,357788416,357788643⟩]
theorem checked35640 : checkPrefixCuts (2^48) 4675338241 10 Manual.Count131072.C035640.packed 64 cuts35640 = true := by
 decide +kernel
def pointBounds35640 : List (Nat × Nat × Nat) := [(4675469312,107412526531742,107412911156707)]
theorem point_links_checked35640 : (cuts35640.take 1).map (fun c => (4675338241-1+2*2^10*c.k,107412168743326+c.lower,107412553368064+c.upper)) = pointBounds35640 := by
 decide +kernel
def cuts35641 : List PrefixCut := [⟨64,357356962,357357182⟩]
theorem checked35641 : checkPrefixCuts (2^48) 4675469313 10 Manual.Count131072.C035641.packed 64 cuts35641 = true := by
 decide +kernel
def cuts35642 : List PrefixCut := [⟨8,42441491,42441518⟩,
⟨64,353373725,353373943⟩]
theorem checked35642 : checkPrefixCuts (2^48) 4675600385 10 Manual.Count131072.C035642.packed 64 cuts35642 = true := by
 decide +kernel
def pointBounds35642 : List (Nat × Nat × Nat) := [(4675616768,107412926330195,107413310955407)]
theorem point_links_checked35642 : (cuts35642.take 1).map (fun c => (4675600385-1+2*2^10*c.k,107412883888704+c.lower,107413268513889+c.upper)) = pointBounds35642 := by
 decide +kernel
def cuts35643 : List PrefixCut := [⟨16,86626220,86626275⟩,
⟨64,350715121,350715338⟩]
theorem checked35643 : checkPrefixCuts (2^48) 4675731457 10 Manual.Count131072.C035643.packed 64 cuts35643 = true := by
 decide +kernel
def pointBounds35643 : List (Nat × Nat × Nat) := [(4675764224,107413323888649,107413708514107)]
theorem point_links_checked35643 : (cuts35643.take 1).map (fun c => (4675731457-1+2*2^10*c.k,107413237262429+c.lower,107413621887832+c.upper)) = pointBounds35643 := by
 decide +kernel
def cuts35644 : List PrefixCut := [⟨24,133517187,133517267⟩,
⟨64,357086133,357086348⟩]
theorem checked35644 : checkPrefixCuts (2^48) 4675862529 10 Manual.Count131072.C035644.packed 64 cuts35644 = true := by
 decide +kernel
def pointBounds35644 : List (Nat × Nat × Nat) := [(4675911680,107413721494737,107414106120437)]
theorem point_links_checked35644 : (cuts35644.take 1).map (fun c => (4675862529-1+2*2^10*c.k,107413587977550+c.lower,107413972603170+c.upper)) = pointBounds35644 := by
 decide +kernel
def cuts35645 : List PrefixCut := [⟨32,178298531,178298643⟩,
⟨64,355571256,355571484⟩]
theorem checked35645 : checkPrefixCuts (2^48) 4675993601 10 Manual.Count131072.C035645.packed 64 cuts35645 = true := by
 decide +kernel
def pointBounds35645 : List (Nat × Nat × Nat) := [(4676059136,107414123362214,107414507988161)]
theorem point_links_checked35645 : (cuts35645.take 1).map (fun c => (4675993601-1+2*2^10*c.k,107413945063683+c.lower,107414329689518+c.upper)) = pointBounds35645 := by
 decide +kernel
def cuts35646 : List PrefixCut := [⟨40,225364544,225364683⟩,
⟨64,360617493,360617716⟩]
theorem checked35646 : checkPrefixCuts (2^48) 4676124673 10 Manual.Count131072.C035646.packed 64 cuts35646 = true := by
 decide +kernel
def pointBounds35646 : List (Nat × Nat × Nat) := [(4676206592,107414525999483,107414910625685)]
theorem point_links_checked35646 : (cuts35646.take 1).map (fun c => (4676124673-1+2*2^10*c.k,107414300634939+c.lower,107414685261002+c.upper)) = pointBounds35646 := by
 decide +kernel
def cuts35647 : List PrefixCut := [⟨48,265686308,265686471⟩,
⟨64,355792071,355792288⟩]
theorem checked35647 : checkPrefixCuts (2^48) 4676255745 10 Manual.Count131072.C035647.packed 64 cuts35647 = true := by
 decide +kernel
def pointBounds35647 : List (Nat × Nat × Nat) := [(4676354048,107414926938740,107415311565189)]
theorem point_links_checked35647 : (cuts35647.take 1).map (fun c => (4676255745-1+2*2^10*c.k,107414661252432+c.lower,107415045878718+c.upper)) = pointBounds35647 := by
 decide +kernel
def cuts35648 : List PrefixCut := [⟨56,311482928,311483119⟩,
⟨64,355661725,355661942⟩]
theorem checked35648 : checkPrefixCuts (2^48) 4676386817 10 Manual.Count131072.C035648.packed 64 cuts35648 = true := by
 decide +kernel
def pointBounds35648 : List (Nat × Nat × Nat) := [(4676501504,107415328527431,107415713154125)]
theorem point_links_checked35648 : (cuts35648.take 1).map (fun c => (4676386817-1+2*2^10*c.k,107415017044503+c.lower,107415401671006+c.upper)) = pointBounds35648 := by
 decide +kernel
def cuts35649 : List PrefixCut := [⟨64,352461797,352462014⟩]
theorem checked35649 : checkPrefixCuts (2^48) 4676517889 10 Manual.Count131072.C035649.packed 64 cuts35649 = true := by
 decide +kernel
def pointBounds35649 : List (Nat × Nat × Nat) := [(4676648960,107415725168025,107416109794962)]
theorem point_links_checked35649 : (cuts35649.take 1).map (fun c => (4676517889-1+2*2^10*c.k,107415372706228+c.lower,107415757332948+c.upper)) = pointBounds35649 := by
 decide +kernel
def cuts35650 : List PrefixCut := [⟨64,352813049,352813267⟩]
theorem checked35650 : checkPrefixCuts (2^48) 4676648961 10 Manual.Count131072.C035650.packed 64 cuts35650 = true := by
 decide +kernel
def cuts35651 : List PrefixCut := [⟨8,43634494,43634521⟩,
⟨64,354789259,354789483⟩]
theorem checked35651 : checkPrefixCuts (2^48) 4676780033 10 Manual.Count131072.C035651.packed 64 cuts35651 = true := by
 decide +kernel
def pointBounds35651 : List (Nat × Nat × Nat) := [(4676796416,107416121615568,107416506242750)]
theorem point_links_checked35651 : (cuts35651.take 1).map (fun c => (4676780033-1+2*2^10*c.k,107416077981074+c.lower,107416462608229+c.upper)) = pointBounds35651 := by
 decide +kernel
def cuts35652 : List PrefixCut := [⟨16,86845111,86845165⟩,
⟨64,350867355,350867572⟩]
theorem checked35652 : checkPrefixCuts (2^48) 4676911105 10 Manual.Count131072.C035652.packed 64 cuts35652 = true := by
 decide +kernel
def pointBounds35652 : List (Nat × Nat × Nat) := [(4676943872,107416519615444,107416904242877)]
theorem point_links_checked35652 : (cuts35652.take 1).map (fun c => (4676911105-1+2*2^10*c.k,107416432770333+c.lower,107416817397712+c.upper)) = pointBounds35652 := by
 decide +kernel
def cuts35653 : List PrefixCut := [⟨24,135650064,135650146⟩,
⟨64,356815549,356815769⟩]
theorem checked35653 : checkPrefixCuts (2^48) 4677042177 10 Manual.Count131072.C035653.packed 64 cuts35653 = true := by
 decide +kernel
def pointBounds35653 : List (Nat × Nat × Nat) := [(4677091328,107416919287752,107417303915430)]
theorem point_links_checked35653 : (cuts35653.take 1).map (fun c => (4677042177-1+2*2^10*c.k,107416783637688+c.lower,107417168265284+c.upper)) = pointBounds35653 := by
 decide +kernel
def cuts35654 : List PrefixCut := [⟨32,174943652,174943762⟩,
⟨64,351509705,351509929⟩]
theorem checked35654 : checkPrefixCuts (2^48) 4677173249 10 Manual.Count131072.C035654.packed 64 cuts35654 = true := by
 decide +kernel
def pointBounds35654 : List (Nat × Nat × Nat) := [(4677238784,107417315396889,107417700024815)]
theorem point_links_checked35654 : (cuts35654.take 1).map (fun c => (4677173249-1+2*2^10*c.k,107417140453237+c.lower,107417525081053+c.upper)) = pointBounds35654 := by
 decide +kernel
def cuts35655 : List PrefixCut := [⟨40,224585567,224585706⟩,
⟨64,358721217,358721440⟩]
theorem checked35655 : checkPrefixCuts (2^48) 4677304321 10 Manual.Count131072.C035655.packed 64 cuts35655 = true := by
 decide +kernel
def pointBounds35655 : List (Nat × Nat × Nat) := [(4677386240,107417716548509,107418101176688)]
theorem point_links_checked35655 : (cuts35655.take 1).map (fun c => (4677304321-1+2*2^10*c.k,107417491962942+c.lower,107417876590982+c.upper)) = pointBounds35655 := by
 decide +kernel
def cuts35656 : List PrefixCut := [⟨48,265920165,265920329⟩,
⟨64,356183727,356183945⟩]
theorem checked35656 : checkPrefixCuts (2^48) 4677435393 10 Manual.Count131072.C035656.packed 64 cuts35656 = true := by
 decide +kernel
def pointBounds35656 : List (Nat × Nat × Nat) := [(4677533696,107418116604324,107418501232751)]
theorem point_links_checked35656 : (cuts35656.take 1).map (fun c => (4677435393-1+2*2^10*c.k,107417850684159+c.lower,107418235312422+c.upper)) = pointBounds35656 := by
 decide +kernel
def cuts35657 : List PrefixCut := [⟨56,311464549,311464746⟩,
⟨64,353887159,353887382⟩]
theorem checked35657 : checkPrefixCuts (2^48) 4677566465 10 Manual.Count131072.C035657.packed 64 cuts35657 = true := by
 decide +kernel
def pointBounds35657 : List (Nat × Nat × Nat) := [(4677681152,107418518332435,107418902961113)]
theorem point_links_checked35657 : (cuts35657.take 1).map (fun c => (4677566465-1+2*2^10*c.k,107418206867886+c.lower,107418591496367+c.upper)) = pointBounds35657 := by
 decide +kernel
def cuts35658 : List PrefixCut := [⟨64,351530448,351530665⟩]
theorem checked35658 : checkPrefixCuts (2^48) 4677697537 10 Manual.Count131072.C035658.packed 64 cuts35658 = true := by
 decide +kernel
def pointBounds35658 : List (Nat × Nat × Nat) := [(4677828608,107418912285493,107419296914414)]
theorem point_links_checked35658 : (cuts35658.take 1).map (fun c => (4677697537-1+2*2^10*c.k,107418560755045+c.lower,107418945383749+c.upper)) = pointBounds35658 := by
 decide +kernel
def cuts35659 : List PrefixCut := [⟨64,353205458,353205685⟩]
theorem checked35659 : checkPrefixCuts (2^48) 4677828609 10 Manual.Count131072.C035659.packed 64 cuts35659 = true := by
 decide +kernel
def cuts35660 : List PrefixCut := [⟨8,44887069,44887096⟩,
⟨64,355301484,355301703⟩]
theorem checked35660 : checkPrefixCuts (2^48) 4677959681 10 Manual.Count131072.C035660.packed 64 cuts35660 = true := by
 decide +kernel
def pointBounds35660 : List (Nat × Nat × Nat) := [(4677976064,107419310378020,107419695007195)]
theorem point_links_checked35660 : (cuts35660.take 1).map (fun c => (4677959681-1+2*2^10*c.k,107419265490951+c.lower,107419650120099+c.upper)) = pointBounds35660 := by
 decide +kernel
def cuts35661 : List PrefixCut := [⟨16,89229950,89230006⟩,
⟨64,354148317,354148536⟩]
theorem checked35661 : checkPrefixCuts (2^48) 4678090753 10 Manual.Count131072.C035661.packed 64 cuts35661 = true := by
 decide +kernel
def pointBounds35661 : List (Nat × Nat × Nat) := [(4678123520,107419710022385,107420094651808)]
theorem point_links_checked35661 : (cuts35661.take 1).map (fun c => (4678090753-1+2*2^10*c.k,107419620792435+c.lower,107420005421802+c.upper)) = pointBounds35661 := by
 decide +kernel
def cuts35662 : List PrefixCut := [⟨24,134412529,134412610⟩,
⟨64,356605235,356605455⟩]
theorem checked35662 : checkPrefixCuts (2^48) 4678221825 10 Manual.Count131072.C035662.packed 64 cuts35662 = true := by
 decide +kernel
def pointBounds35662 : List (Nat × Nat × Nat) := [(4678270976,107420109353281,107420493982948)]
theorem point_links_checked35662 : (cuts35662.take 1).map (fun c => (4678221825-1+2*2^10*c.k,107419974940752+c.lower,107420359570338+c.upper)) = pointBounds35662 := by
 decide +kernel
def cuts35663 : List PrefixCut := [⟨32,174538559,174538665⟩,
⟨64,349796649,349796863⟩]
theorem checked35663 : checkPrefixCuts (2^48) 4678352897 10 Manual.Count131072.C035663.packed 64 cuts35663 = true := by
 decide +kernel
def pointBounds35663 : List (Nat × Nat × Nat) := [(4678418432,107420506084546,107420890714458)]
theorem point_links_checked35663 : (cuts35663.take 1).map (fun c => (4678352897-1+2*2^10*c.k,107420331545987+c.lower,107420716175793+c.upper)) = pointBounds35663 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000176
