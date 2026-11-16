import PlattAssemblyKernel
import PlattCertificates.Count131072.C053616
import PlattCertificates.Count131072.C053617
import PlattCertificates.Count131072.C053618
import PlattCertificates.Count131072.C053619
import PlattCertificates.Count131072.C053620
import PlattCertificates.Count131072.C053621
import PlattCertificates.Count131072.C053622
import PlattCertificates.Count131072.C053623
import PlattCertificates.Count131072.C053624
import PlattCertificates.Count131072.C053625
import PlattCertificates.Count131072.C053626
import PlattCertificates.Count131072.C053627
import PlattCertificates.Count131072.C053628
import PlattCertificates.Count131072.C053629
import PlattCertificates.Count131072.C053630
import PlattCertificates.Count131072.C053631
import PlattCertificates.Count131072.C053632
import PlattCertificates.Count131072.C053633
import PlattCertificates.Count131072.C053634
import PlattCertificates.Count131072.C053635
import PlattCertificates.Count131072.C053636
import PlattCertificates.Count131072.C053637
import PlattCertificates.Count131072.C053638
import PlattCertificates.Count131072.C053639
import PlattCertificates.Count131072.C053640
import PlattCertificates.Count131072.C053641
import PlattCertificates.Count131072.C053642
import PlattCertificates.Count131072.C053643
import PlattCertificates.Count131072.C053644
import PlattCertificates.Count131072.C053645
import PlattCertificates.Count131072.C053646
import PlattCertificates.Count131072.C053647
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000113
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts53616 : List PrefixCut := [⟨64,229853707,229853838⟩]
theorem checked53616 : checkPrefixCuts (2^48) 7031488513 10 Manual.Count131072.C053616.packed 64 cuts53616 = true := by
 decide +kernel
def cuts53617 : List PrefixCut := [⟨37,133579001,133579079⟩,
⟨64,229809414,229809549⟩]
theorem checked53617 : checkPrefixCuts (2^48) 7031619585 10 Manual.Count131072.C053617.packed 64 cuts53617 = true := by
 decide +kernel
def pointBounds53617 : List (Nat × Nat × Nat) := [(7031695360,112524861999996,112525249615357)]
theorem point_links_checked53617 : (cuts53617.take 1).map (fun c => (7031619585-1+2*2^10*c.k,112524728420995+c.lower,112525116036278+c.upper)) = pointBounds53617 := by
 decide +kernel
def cuts53618 : List PrefixCut := [⟨64,230165370,230165502⟩]
theorem checked53618 : checkPrefixCuts (2^48) 7031750657 10 Manual.Count131072.C053618.packed 64 cuts53618 = true := by
 decide +kernel
def cuts53619 : List PrefixCut := [⟨17,63044558,63044593⟩,
⟨64,235524832,235524966⟩]
theorem checked53619 : checkPrefixCuts (2^48) 7031881729 10 Manual.Count131072.C053619.packed 64 cuts53619 = true := by
 decide +kernel
def pointBounds53619 : List (Nat × Nat × Nat) := [(7031916544,112525251440337,112525639055922)]
theorem point_links_checked53619 : (cuts53619.take 1).map (fun c => (7031881729-1+2*2^10*c.k,112525188395779+c.lower,112525576011329+c.upper)) = pointBounds53619 := by
 decide +kernel
def cuts53620 : List PrefixCut := [⟨61,220029984,220030110⟩,
⟨64,231317575,231317707⟩]
theorem checked53620 : checkPrefixCuts (2^48) 7032012801 10 Manual.Count131072.C053620.packed 64 cuts53620 = true := by
 decide +kernel
def pointBounds53620 : List (Nat × Nat × Nat) := [(7032137728,112525643950595,112526031566405)]
theorem point_links_checked53620 : (cuts53620.take 1).map (fun c => (7032012801-1+2*2^10*c.k,112525423920611+c.lower,112525811536295+c.upper)) = pointBounds53620 := by
 decide +kernel
def cuts53621 : List PrefixCut := [⟨64,230832954,230833085⟩]
theorem checked53621 : checkPrefixCuts (2^48) 7032143873 10 Manual.Count131072.C053621.packed 64 cuts53621 = true := by
 decide +kernel
def cuts53622 : List PrefixCut := [⟨41,147215311,147215393⟩,
⟨64,228827385,228827514⟩]
theorem checked53622 : checkPrefixCuts (2^48) 7032274945 10 Manual.Count131072.C053622.packed 64 cuts53622 = true := by
 decide +kernel
def pointBounds53622 : List (Nat × Nat × Nat) := [(7032358912,112526033286451,112526420902480)]
theorem point_links_checked53622 : (cuts53622.take 1).map (fun c => (7032274945-1+2*2^10*c.k,112525886071140+c.lower,112526273687087+c.upper)) = pointBounds53622 := by
 decide +kernel
def cuts53623 : List PrefixCut := [⟨64,232945689,232945820⟩]
theorem checked53623 : checkPrefixCuts (2^48) 7032406017 10 Manual.Count131072.C053623.packed 64 cuts53623 = true := by
 decide +kernel
def cuts53624 : List PrefixCut := [⟨21,75005978,75006021⟩,
⟨64,228738786,228738917⟩]
theorem checked53624 : checkPrefixCuts (2^48) 7032537089 10 Manual.Count131072.C053624.packed 64 cuts53624 = true := by
 decide +kernel
def pointBounds53624 : List (Nat × Nat × Nat) := [(7032580096,112526422850192,112526810466442)]
theorem point_links_checked53624 : (cuts53624.take 1).map (fun c => (7032537089-1+2*2^10*c.k,112526347844214+c.lower,112526735460421+c.upper)) = pointBounds53624 := by
 decide +kernel
def cuts53625 : List PrefixCut := [⟨64,230415520,230415651⟩]
theorem checked53625 : checkPrefixCuts (2^48) 7032668161 10 Manual.Count131072.C053625.packed 64 cuts53625 = true := by
 decide +kernel
def cuts53626 : List PrefixCut := [⟨1,3401969,3401971⟩,
⟨64,232412378,232412512⟩]
theorem checked53626 : checkPrefixCuts (2^48) 7032799233 10 Manual.Count131072.C053626.packed 64 cuts53626 = true := by
 decide +kernel
def pointBounds53626 : List (Nat × Nat × Nat) := [(7032801280,112526810400489,112527198016960)]
theorem point_links_checked53626 : (cuts53626.take 1).map (fun c => (7032799233-1+2*2^10*c.k,112526806998520+c.lower,112527194614989+c.upper)) = pointBounds53626 := by
 decide +kernel
def cuts53627 : List PrefixCut := [⟨45,163850731,163850824⟩,
⟨64,232328009,232328142⟩]
theorem checked53627 : checkPrefixCuts (2^48) 7032930305 10 Manual.Count131072.C053627.packed 64 cuts53627 = true := by
 decide +kernel
def pointBounds53627 : List (Nat × Nat × Nat) := [(7033022464,112527203261629,112527590878325)]
theorem point_links_checked53627 : (cuts53627.take 1).map (fun c => (7032930305-1+2*2^10*c.k,112527039410898+c.lower,112527427027501+c.upper)) = pointBounds53627 := by
 decide +kernel
def cuts53628 : List PrefixCut := [⟨64,234124614,234124746⟩]
theorem checked53628 : checkPrefixCuts (2^48) 7033061377 10 Manual.Count131072.C053628.packed 64 cuts53628 = true := by
 decide +kernel
def cuts53629 : List PrefixCut := [⟨25,87805601,87805654⟩,
⟨64,229958104,229958239⟩]
theorem checked53629 : checkPrefixCuts (2^48) 7033192449 10 Manual.Count131072.C053629.packed 64 cuts53629 = true := by
 decide +kernel
def pointBounds53629 : List (Nat × Nat × Nat) := [(7033243648,112527593669122,112527981286043)]
theorem point_links_checked53629 : (cuts53629.take 1).map (fun c => (7033192449-1+2*2^10*c.k,112527505863521+c.lower,112527893480389+c.upper)) = pointBounds53629 := by
 decide +kernel
def cuts53630 : List PrefixCut := [⟨64,227472592,227472724⟩]
theorem checked53630 : checkPrefixCuts (2^48) 7033323521 10 Manual.Count131072.C053630.packed 64 cuts53630 = true := by
 decide +kernel
def cuts53631 : List PrefixCut := [⟨5,18128792,18128802⟩,
⟨64,231550292,231550423⟩]
theorem checked53631 : checkPrefixCuts (2^48) 7033454593 10 Manual.Count131072.C053631.packed 64 cuts53631 = true := by
 decide +kernel
def pointBounds53631 : List (Nat × Nat × Nat) := [(7033464832,112527981423009,112528369040154)]
theorem point_links_checked53631 : (cuts53631.take 1).map (fun c => (7033454593-1+2*2^10*c.k,112527963294217+c.lower,112528350911352+c.upper)) = pointBounds53631 := by
 decide +kernel
def cuts53632 : List PrefixCut := [⟨49,176681266,176681364⟩,
⟨64,230145360,230145490⟩]
theorem checked53632 : checkPrefixCuts (2^48) 7033585665 10 Manual.Count131072.C053632.packed 64 cuts53632 = true := by
 decide +kernel
def pointBounds53632 : List (Nat × Nat × Nat) := [(7033686016,112528371525775,112528759143139)]
theorem point_links_checked53632 : (cuts53632.take 1).map (fun c => (7033585665-1+2*2^10*c.k,112528194844509+c.lower,112528582461775+c.upper)) = pointBounds53632 := by
 decide +kernel
def cuts53633 : List PrefixCut := [⟨64,231381607,231381740⟩]
theorem checked53633 : checkPrefixCuts (2^48) 7033716737 10 Manual.Count131072.C053633.packed 64 cuts53633 = true := by
 decide +kernel
def cuts53634 : List PrefixCut := [⟨29,104084296,104084354⟩,
⟨64,231537349,231537478⟩]
theorem checked53634 : checkPrefixCuts (2^48) 7033847809 10 Manual.Count131072.C053634.packed 64 cuts53634 = true := by
 decide +kernel
def pointBounds53634 : List (Nat × Nat × Nat) := [(7033907200,112528760455772,112529148073359)]
theorem point_links_checked53634 : (cuts53634.take 1).map (fun c => (7033847809-1+2*2^10*c.k,112528656371476+c.lower,112529043989005+c.upper)) = pointBounds53634 := by
 decide +kernel
def cuts53635 : List PrefixCut := [⟨64,231453023,231453154⟩]
theorem checked53635 : checkPrefixCuts (2^48) 7033978881 10 Manual.Count131072.C053635.packed 64 cuts53635 = true := by
 decide +kernel
def cuts53636 : List PrefixCut := [⟨9,31812447,31812465⟩,
⟨64,229167817,229167951⟩]
theorem checked53636 : checkPrefixCuts (2^48) 7034109953 10 Manual.Count131072.C053636.packed 64 cuts53636 = true := by
 decide +kernel
def pointBounds53636 : List (Nat × Nat × Nat) := [(7034128384,112529151174295,112529538792102)]
theorem point_links_checked53636 : (cuts53636.take 1).map (fun c => (7034109953-1+2*2^10*c.k,112529119361848+c.lower,112529506979637+c.upper)) = pointBounds53636 := by
 decide +kernel
def cuts53637 : List PrefixCut := [⟨53,191029955,191030063⟩,
⟨64,230884180,230884311⟩]
theorem checked53637 : checkPrefixCuts (2^48) 7034241025 10 Manual.Count131072.C053637.packed 64 cuts53637 = true := by
 decide +kernel
def pointBounds53637 : List (Nat × Nat × Nat) := [(7034349568,112529539559620,112529927177651)]
theorem point_links_checked53637 : (cuts53637.take 1).map (fun c => (7034241025-1+2*2^10*c.k,112529348529665+c.lower,112529736147588+c.upper)) = pointBounds53637 := by
 decide +kernel
def cuts53638 : List PrefixCut := [⟨64,232840556,232840687⟩]
theorem checked53638 : checkPrefixCuts (2^48) 7034372097 10 Manual.Count131072.C053638.packed 64 cuts53638 = true := by
 decide +kernel
def cuts53639 : List PrefixCut := [⟨33,117398955,117399021⟩,
⟨64,228434765,228434894⟩]
theorem checked53639 : checkPrefixCuts (2^48) 7034503169 10 Manual.Count131072.C053639.packed 64 cuts53639 = true := by
 decide +kernel
def pointBounds53639 : List (Nat × Nat × Nat) := [(7034570752,112529929653356,112530317271607)]
theorem point_links_checked53639 : (cuts53639.take 1).map (fun c => (7034503169-1+2*2^10*c.k,112529812254401+c.lower,112530199872586+c.upper)) = pointBounds53639 := by
 decide +kernel
def cuts53640 : List PrefixCut := [⟨64,233792192,233792321⟩]
theorem checked53640 : checkPrefixCuts (2^48) 7034634241 10 Manual.Count131072.C053640.packed 64 cuts53640 = true := by
 decide +kernel
def cuts53641 : List PrefixCut := [⟨13,46493834,46493863⟩,
⟨64,232547459,232547591⟩]
theorem checked53641 : checkPrefixCuts (2^48) 7034765313 10 Manual.Count131072.C053641.packed 64 cuts53641 = true := by
 decide +kernel
def pointBounds53641 : List (Nat × Nat × Nat) := [(7034791936,112530320975192,112530708593664)]
theorem point_links_checked53641 : (cuts53641.take 1).map (fun c => (7034765313-1+2*2^10*c.k,112530274481358+c.lower,112530662099801+c.upper)) = pointBounds53641 := by
 decide +kernel
def cuts53642 : List PrefixCut := [⟨57,204655775,204655890⟩,
⟨64,230222505,230222634⟩]
theorem checked53642 : checkPrefixCuts (2^48) 7034896385 10 Manual.Count131072.C053642.packed 64 cuts53642 = true := by
 decide +kernel
def pointBounds53642 : List (Nat × Nat × Nat) := [(7035013120,112530711684592,112531099303282)]
theorem point_links_checked53642 : (cuts53642.take 1).map (fun c => (7034896385-1+2*2^10*c.k,112530507028817+c.lower,112530894647392+c.upper)) = pointBounds53642 := by
 decide +kernel
def cuts53643 : List PrefixCut := [⟨64,232858893,232859031⟩]
theorem checked53643 : checkPrefixCuts (2^48) 7035027457 10 Manual.Count131072.C053643.packed 64 cuts53643 = true := by
 decide +kernel
def cuts53644 : List PrefixCut := [⟨37,133671844,133671919⟩,
⟨64,230934100,230934231⟩]
theorem checked53644 : checkPrefixCuts (2^48) 7035158529 10 Manual.Count131072.C053644.packed 64 cuts53644 = true := by
 decide +kernel
def pointBounds53644 : List (Nat × Nat × Nat) := [(7035234304,112531103782059,112531491400976)]
theorem point_links_checked53644 : (cuts53644.take 1).map (fun c => (7035158529-1+2*2^10*c.k,112530970110215+c.lower,112531357729057+c.upper)) = pointBounds53644 := by
 decide +kernel
def cuts53645 : List PrefixCut := [⟨64,231930021,231930154⟩]
theorem checked53645 : checkPrefixCuts (2^48) 7035289601 10 Manual.Count131072.C053645.packed 64 cuts53645 = true := by
 decide +kernel
def cuts53646 : List PrefixCut := [⟨17,62092655,62092691⟩,
⟨64,231965699,231965833⟩]
theorem checked53646 : checkPrefixCuts (2^48) 7035420673 10 Manual.Count131072.C053646.packed 64 cuts53646 = true := by
 decide +kernel
def pointBounds53646 : List (Nat × Nat × Nat) := [(7035455488,112531495066991,112531882686133)]
theorem point_links_checked53646 : (cuts53646.take 1).map (fun c => (7035420673-1+2*2^10*c.k,112531432974336+c.lower,112531820593442+c.upper)) = pointBounds53646 := by
 decide +kernel
def cuts53647 : List PrefixCut := [⟨61,223039875,223040000⟩,
⟨64,234281780,234281912⟩]
theorem checked53647 : checkPrefixCuts (2^48) 7035551745 10 Manual.Count131072.C053647.packed 64 cuts53647 = true := by
 decide +kernel
def pointBounds53647 : List (Nat × Nat × Nat) := [(7035676672,112531887979910,112532275599275)]
theorem point_links_checked53647 : (cuts53647.take 1).map (fun c => (7035551745-1+2*2^10*c.k,112531664940035+c.lower,112532052559275+c.upper)) = pointBounds53647 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000113
