import PlattAssemblyKernel
import PlattCertificates.Count131072.C043712
import PlattCertificates.Count131072.C043713
import PlattCertificates.Count131072.C043714
import PlattCertificates.Count131072.C043715
import PlattCertificates.Count131072.C043716
import PlattCertificates.Count131072.C043717
import PlattCertificates.Count131072.C043718
import PlattCertificates.Count131072.C043719
import PlattCertificates.Count131072.C043720
import PlattCertificates.Count131072.C043721
import PlattCertificates.Count131072.C043722
import PlattCertificates.Count131072.C043723
import PlattCertificates.Count131072.C043724
import PlattCertificates.Count131072.C043725
import PlattCertificates.Count131072.C043726
import PlattCertificates.Count131072.C043727
import PlattCertificates.Count131072.C043728
import PlattCertificates.Count131072.C043729
import PlattCertificates.Count131072.C043730
import PlattCertificates.Count131072.C043731
import PlattCertificates.Count131072.C043732
import PlattCertificates.Count131072.C043733
import PlattCertificates.Count131072.C043734
import PlattCertificates.Count131072.C043735
import PlattCertificates.Count131072.C043736
import PlattCertificates.Count131072.C043737
import PlattCertificates.Count131072.C043738
import PlattCertificates.Count131072.C043739
import PlattCertificates.Count131072.C043740
import PlattCertificates.Count131072.C043741
import PlattCertificates.Count131072.C043742
import PlattCertificates.Count131072.C043743
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000116
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts43712 : List PrefixCut := [⟨64,286511093,286511264⟩]
theorem checked43712 : checkPrefixCuts (2^48) 5733351425 10 Manual.Count131072.C043712.packed 64 cuts43712 = true := by
 decide +kernel
def cuts43713 : List PrefixCut := [⟨6,26755754,26755770⟩,
⟨64,288713674,288713843⟩]
theorem checked43713 : checkPrefixCuts (2^48) 5733482497 10 Manual.Count131072.C043713.packed 64 cuts43713 = true := by
 decide +kernel
def pointBounds43713 : List (Nat × Nat × Nat) := [(5733494784,109979661645398,109980047804661)]
theorem point_links_checked43713 : (cuts43713.take 1).map (fun c => (5733482497-1+2*2^10*c.k,109979634889644+c.lower,109980021048891+c.upper)) = pointBounds43713 := by
 decide +kernel
def cuts43714 : List PrefixCut := [⟨30,135346085,135346162⟩,
⟨64,289983474,289983640⟩]
theorem checked43714 : checkPrefixCuts (2^48) 5733613569 10 Manual.Count131072.C043714.packed 64 cuts43714 = true := by
 decide +kernel
def pointBounds43714 : List (Nat × Nat × Nat) := [(5733675008,109980058949403,109980445108896)]
theorem point_links_checked43714 : (cuts43714.take 1).map (fun c => (5733613569-1+2*2^10*c.k,109979923603318+c.lower,109980309762734+c.upper)) = pointBounds43714 := by
 decide +kernel
def cuts43715 : List PrefixCut := [⟨54,240592369,240592506⟩,
⟨64,284429651,284429816⟩]
theorem checked43715 : checkPrefixCuts (2^48) 5733744641 10 Manual.Count131072.C043715.packed 64 cuts43715 = true := by
 decide +kernel
def pointBounds43715 : List (Nat × Nat × Nat) := [(5733855232,109980454179161,109980840338880)]
theorem point_links_checked43715 : (cuts43715.take 1).map (fun c => (5733744641-1+2*2^10*c.k,109980213586792+c.lower,109980599746374+c.upper)) = pointBounds43715 := by
 decide +kernel
def cuts43716 : List PrefixCut := [⟨64,290117469,290117639⟩]
theorem checked43716 : checkPrefixCuts (2^48) 5733875713 10 Manual.Count131072.C043716.packed 64 cuts43716 = true := by
 decide +kernel
def cuts43717 : List PrefixCut := [⟨14,62833367,62833405⟩,
⟨64,291190806,291190978⟩]
theorem checked43717 : checkPrefixCuts (2^48) 5734006785 10 Manual.Count131072.C043717.packed 64 cuts43717 = true := by
 decide +kernel
def pointBounds43717 : List (Nat × Nat × Nat) := [(5734035456,109980850967279,109981237127234)]
theorem point_links_checked43717 : (cuts43717.take 1).map (fun c => (5734006785-1+2*2^10*c.k,109980788133912+c.lower,109981174293829+c.upper)) = pointBounds43717 := by
 decide +kernel
def cuts43718 : List PrefixCut := [⟨38,171658054,171658156⟩,
⟨64,286717224,286717396⟩]
theorem checked43718 : checkPrefixCuts (2^48) 5734137857 10 Manual.Count131072.C043718.packed 64 cuts43718 = true := by
 decide +kernel
def pointBounds43718 : List (Nat × Nat × Nat) := [(5734215680,109981250982772,109981637142963)]
theorem point_links_checked43718 : (cuts43718.take 1).map (fun c => (5734137857-1+2*2^10*c.k,109981079324718+c.lower,109981465484807+c.upper)) = pointBounds43718 := by
 decide +kernel
def cuts43719 : List PrefixCut := [⟨62,275322843,275322998⟩,
⟨64,284305461,284305621⟩]
theorem checked43719 : checkPrefixCuts (2^48) 5734268929 10 Manual.Count131072.C043719.packed 64 cuts43719 = true := by
 decide +kernel
def pointBounds43719 : List (Nat × Nat × Nat) := [(5734395904,109981641364785,109982027525201)]
theorem point_links_checked43719 : (cuts43719.take 1).map (fun c => (5734268929-1+2*2^10*c.k,109981366041942+c.lower,109981752202203+c.upper)) = pointBounds43719 := by
 decide +kernel
def cuts43720 : List PrefixCut := [⟨64,286016957,286017123⟩]
theorem checked43720 : checkPrefixCuts (2^48) 5734400001 10 Manual.Count131072.C043720.packed 64 cuts43720 = true := by
 decide +kernel
def cuts43721 : List PrefixCut := [⟨22,99984136,99984192⟩,
⟨64,286893911,286894080⟩]
theorem checked43721 : checkPrefixCuts (2^48) 5734531073 10 Manual.Count131072.C043721.packed 64 cuts43721 = true := by
 decide +kernel
def pointBounds43721 : List (Nat × Nat × Nat) := [(5734576128,109982036348496,109982422509139)]
theorem point_links_checked43721 : (cuts43721.take 1).map (fun c => (5734531073-1+2*2^10*c.k,109981936364360+c.lower,109982322524947+c.upper)) = pointBounds43721 := by
 decide +kernel
def cuts43722 : List PrefixCut := [⟨46,204282124,204282237⟩,
⟨64,284187815,284187974⟩]
theorem checked43722 : checkPrefixCuts (2^48) 5734662145 10 Manual.Count131072.C043722.packed 64 cuts43722 = true := by
 decide +kernel
def pointBounds43722 : List (Nat × Nat × Nat) := [(5734756352,109982427540395,109982813701264)]
theorem point_links_checked43722 : (cuts43722.take 1).map (fun c => (5734662145-1+2*2^10*c.k,109982223258271+c.lower,109982609419027+c.upper)) = pointBounds43722 := by
 decide +kernel
def cuts43723 : List PrefixCut := [⟨64,285604683,285604854⟩]
theorem checked43723 : checkPrefixCuts (2^48) 5734793217 10 Manual.Count131072.C043723.packed 64 cuts43723 = true := by
 decide +kernel
def cuts43724 : List PrefixCut := [⟨6,26012818,26012832⟩,
⟨64,287561331,287561492⟩]
theorem checked43724 : checkPrefixCuts (2^48) 5734924289 10 Manual.Count131072.C043724.packed 64 cuts43724 = true := by
 decide +kernel
def pointBounds43724 : List (Nat × Nat × Nat) := [(5734936576,109982819063587,109983205224687)]
theorem point_links_checked43724 : (cuts43724.take 1).map (fun c => (5734924289-1+2*2^10*c.k,109982793050769+c.lower,109983179211855+c.upper)) = pointBounds43724 := by
 decide +kernel
def cuts43725 : List PrefixCut := [⟨30,134526777,134526856⟩,
⟨64,285689785,285689949⟩]
theorem checked43725 : checkPrefixCuts (2^48) 5735055361 10 Manual.Count131072.C043725.packed 64 cuts43725 = true := by
 decide +kernel
def pointBounds43725 : List (Nat × Nat × Nat) := [(5735116800,109983215138877,109983601300203)]
theorem point_links_checked43725 : (cuts43725.take 1).map (fun c => (5735055361-1+2*2^10*c.k,109983080612100+c.lower,109983466773347+c.upper)) = pointBounds43725 := by
 decide +kernel
def cuts43726 : List PrefixCut := [⟨54,241071735,241071878⟩,
⟨64,284996151,284996320⟩]
theorem checked43726 : checkPrefixCuts (2^48) 5735186433 10 Manual.Count131072.C043726.packed 64 cuts43726 = true := by
 decide +kernel
def pointBounds43726 : List (Nat × Nat × Nat) := [(5735297024,109983607373620,109983993535174)]
theorem point_links_checked43726 : (cuts43726.take 1).map (fun c => (5735186433-1+2*2^10*c.k,109983366301885+c.lower,109983752463296+c.upper)) = pointBounds43726 := by
 decide +kernel
def cuts43727 : List PrefixCut := [⟨64,286265633,286265805⟩]
theorem checked43727 : checkPrefixCuts (2^48) 5735317505 10 Manual.Count131072.C043727.packed 64 cuts43727 = true := by
 decide +kernel
def cuts43728 : List PrefixCut := [⟨14,64240784,64240820⟩,
⟨64,288320292,288320453⟩]
theorem checked43728 : checkPrefixCuts (2^48) 5735448577 10 Manual.Count131072.C043728.packed 64 cuts43728 = true := by
 decide +kernel
def pointBounds43728 : List (Nat × Nat × Nat) := [(5735477248,109984001804453,109984387966241)]
theorem point_links_checked43728 : (cuts43728.take 1).map (fun c => (5735448577-1+2*2^10*c.k,109983937563669+c.lower,109984323725421+c.upper)) = pointBounds43728 := by
 decide +kernel
def cuts43729 : List PrefixCut := [⟨38,175737207,175737305⟩,
⟨64,291160038,291160206⟩]
theorem checked43729 : checkPrefixCuts (2^48) 5735579649 10 Manual.Count131072.C043729.packed 64 cuts43729 = true := by
 decide +kernel
def pointBounds43729 : List (Nat × Nat × Nat) := [(5735657472,109984401621168,109984787783179)]
theorem point_links_checked43729 : (cuts43729.take 1).map (fun c => (5735579649-1+2*2^10*c.k,109984225883961+c.lower,109984612045874+c.upper)) = pointBounds43729 := by
 decide +kernel
def cuts43730 : List PrefixCut := [⟨62,277952682,277952842⟩,
⟨64,286638604,286638769⟩]
theorem checked43730 : checkPrefixCuts (2^48) 5735710721 10 Manual.Count131072.C043730.packed 64 cuts43730 = true := by
 decide +kernel
def pointBounds43730 : List (Nat × Nat × Nat) := [(5735837696,109984794996681,109985181158922)]
theorem point_links_checked43730 : (cuts43730.take 1).map (fun c => (5735710721-1+2*2^10*c.k,109984517043999+c.lower,109984903206080+c.upper)) = pointBounds43730 := by
 decide +kernel
def cuts43731 : List PrefixCut := [⟨64,284129359,284129525⟩]
theorem checked43731 : checkPrefixCuts (2^48) 5735841793 10 Manual.Count131072.C043731.packed 64 cuts43731 = true := by
 decide +kernel
def cuts43732 : List PrefixCut := [⟨22,97456340,97456397⟩,
⟨64,282307230,282307395⟩]
theorem checked43732 : checkPrefixCuts (2^48) 5735972865 10 Manual.Count131072.C043732.packed 64 cuts43732 = true := by
 decide +kernel
def pointBounds43732 : List (Nat × Nat × Nat) := [(5736017920,109985185268302,109985571430771)]
theorem point_links_checked43732 : (cuts43732.take 1).map (fun c => (5735972865-1+2*2^10*c.k,109985087811962+c.lower,109985473974374+c.upper)) = pointBounds43732 := by
 decide +kernel
def cuts43733 : List PrefixCut := [⟨46,206929627,206929753⟩,
⟨64,287747553,287747726⟩]
theorem checked43733 : checkPrefixCuts (2^48) 5736103937 10 Manual.Count131072.C043733.packed 64 cuts43733 = true := by
 decide +kernel
def pointBounds43733 : List (Nat × Nat × Nat) := [(5736198144,109985577048819,109985963211522)]
theorem point_links_checked43733 : (cuts43733.take 1).map (fun c => (5736103937-1+2*2^10*c.k,109985370119192+c.lower,109985756281769+c.upper)) = pointBounds43733 := by
 decide +kernel
def cuts43734 : List PrefixCut := [⟨64,285042174,285042335⟩]
theorem checked43734 : checkPrefixCuts (2^48) 5736235009 10 Manual.Count131072.C043734.packed 64 cuts43734 = true := by
 decide +kernel
def cuts43735 : List PrefixCut := [⟨6,25221182,25221198⟩,
⟨64,283465527,283465689⟩]
theorem checked43735 : checkPrefixCuts (2^48) 5736366081 10 Manual.Count131072.C043735.packed 64 cuts43735 = true := by
 decide +kernel
def pointBounds43735 : List (Nat × Nat × Nat) := [(5736378368,109985968130101,109986354293028)]
theorem point_links_checked43735 : (cuts43735.take 1).map (fun c => (5736366081-1+2*2^10*c.k,109985942908919+c.lower,109986329071830+c.upper)) = pointBounds43735 := by
 decide +kernel
def cuts43736 : List PrefixCut := [⟨30,135081790,135081863⟩,
⟨64,289886794,289886953⟩]
theorem checked43736 : checkPrefixCuts (2^48) 5736497153 10 Manual.Count131072.C043736.packed 64 cuts43736 = true := by
 decide +kernel
def pointBounds43736 : List (Nat × Nat × Nat) := [(5736558592,109986361456236,109986747619382)]
theorem point_links_checked43736 : (cuts43736.take 1).map (fun c => (5736497153-1+2*2^10*c.k,109986226374446+c.lower,109986612537519+c.upper)) = pointBounds43736 := by
 decide +kernel
def cuts43737 : List PrefixCut := [⟨54,240814880,240815019⟩,
⟨64,285905825,285905992⟩]
theorem checked43737 : checkPrefixCuts (2^48) 5736628225 10 Manual.Count131072.C043737.packed 64 cuts43737 = true := by
 decide +kernel
def pointBounds43737 : List (Nat × Nat × Nat) := [(5736738816,109986757076120,109987143239491)]
theorem point_links_checked43737 : (cuts43737.take 1).map (fun c => (5736628225-1+2*2^10*c.k,109986516261240+c.lower,109986902424472+c.upper)) = pointBounds43737 := by
 decide +kernel
def cuts43738 : List PrefixCut := [⟨64,286242774,286242938⟩]
theorem checked43738 : checkPrefixCuts (2^48) 5736759297 10 Manual.Count131072.C043738.packed 64 cuts43738 = true := by
 decide +kernel
def cuts43739 : List PrefixCut := [⟨14,61575188,61575225⟩,
⟨64,283733953,283734120⟩]
theorem checked43739 : checkPrefixCuts (2^48) 5736890369 10 Manual.Count131072.C043739.packed 64 cuts43739 = true := by
 decide +kernel
def pointBounds43739 : List (Nat × Nat × Nat) := [(5736919040,109987149985027,109987536148627)]
theorem point_links_checked43739 : (cuts43739.take 1).map (fun c => (5736890369-1+2*2^10*c.k,109987088409839+c.lower,109987474573402+c.upper)) = pointBounds43739 := by
 decide +kernel
def cuts43740 : List PrefixCut := [⟨38,169756480,169756579⟩,
⟨64,283089714,283089881⟩]
theorem checked43740 : checkPrefixCuts (2^48) 5737021441 10 Manual.Count131072.C043740.packed 64 cuts43740 = true := by
 decide +kernel
def pointBounds43740 : List (Nat × Nat × Nat) := [(5737099264,109987541900272,109987928064101)]
theorem point_links_checked43740 : (cuts43740.take 1).map (fun c => (5737021441-1+2*2^10*c.k,109987372143792+c.lower,109987758307522+c.upper)) = pointBounds43740 := by
 decide +kernel
def cuts43741 : List PrefixCut := [⟨62,280090592,280090757⟩,
⟨64,289510242,289510411⟩]
theorem checked43741 : checkPrefixCuts (2^48) 5737152513 10 Manual.Count131072.C043741.packed 64 cuts43741 = true := by
 decide +kernel
def pointBounds43741 : List (Nat × Nat × Nat) := [(5737279488,109987935324098,109988321488160)]
theorem point_links_checked43741 : (cuts43741.take 1).map (fun c => (5737152513-1+2*2^10*c.k,109987655233506+c.lower,109988041397403+c.upper)) = pointBounds43741 := by
 decide +kernel
def cuts43742 : List PrefixCut := [⟨64,284107001,284107165⟩]
theorem checked43742 : checkPrefixCuts (2^48) 5737283585 10 Manual.Count131072.C043742.packed 64 cuts43742 = true := by
 decide +kernel
def cuts43743 : List PrefixCut := [⟨22,95812900,95812956⟩,
⟨64,282138151,282138318⟩]
theorem checked43743 : checkPrefixCuts (2^48) 5737414657 10 Manual.Count131072.C043743.packed 64 cuts43743 = true := by
 decide +kernel
def pointBounds43743 : List (Nat × Nat × Nat) := [(5737459712,109988324663649,109988710827935)]
theorem point_links_checked43743 : (cuts43743.take 1).map (fun c => (5737414657-1+2*2^10*c.k,109988228850749+c.lower,109988615014979+c.upper)) = pointBounds43743 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000116
