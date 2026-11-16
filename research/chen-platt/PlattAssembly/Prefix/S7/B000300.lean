import PlattAssemblyKernel
import PlattCertificates.Count131072.C069600
import PlattCertificates.Count131072.C069601
import PlattCertificates.Count131072.C069602
import PlattCertificates.Count131072.C069603
import PlattCertificates.Count131072.C069604
import PlattCertificates.Count131072.C069605
import PlattCertificates.Count131072.C069606
import PlattCertificates.Count131072.C069607
import PlattCertificates.Count131072.C069608
import PlattCertificates.Count131072.C069609
import PlattCertificates.Count131072.C069610
import PlattCertificates.Count131072.C069611
import PlattCertificates.Count131072.C069612
import PlattCertificates.Count131072.C069613
import PlattCertificates.Count131072.C069614
import PlattCertificates.Count131072.C069615
import PlattCertificates.Count131072.C069616
import PlattCertificates.Count131072.C069617
import PlattCertificates.Count131072.C069618
import PlattCertificates.Count131072.C069619
import PlattCertificates.Count131072.C069620
import PlattCertificates.Count131072.C069621
import PlattCertificates.Count131072.C069622
import PlattCertificates.Count131072.C069623
import PlattCertificates.Count131072.C069624
import PlattCertificates.Count131072.C069625
import PlattCertificates.Count131072.C069626
import PlattCertificates.Count131072.C069627
import PlattCertificates.Count131072.C069628
import PlattCertificates.Count131072.C069629
import PlattCertificates.Count131072.C069630
import PlattCertificates.Count131072.C069631
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000300
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts69600 : List PrefixCut := [⟨64,176688817,176688912⟩]
theorem checked69600 : checkPrefixCuts (2^48) 9126543361 10 Manual.Count131072.C069600.packed 64 cuts69600 = true := by
 decide +kernel
def cuts69601 : List PrefixCut := [⟨14,38489385,38489409⟩,
⟨64,176069452,176069555⟩]
theorem checked69601 : checkPrefixCuts (2^48) 9126674433 10 Manual.Count131072.C069601.packed 64 cuts69601 = true := by
 decide +kernel
def pointBounds69601 : List (Nat × Nat × Nat) := [(9126703104,115743675868659,115744065332671)]
theorem point_links_checked69601 : (cuts69601.take 1).map (fun c => (9126674433-1+2*2^10*c.k,115743637379274+c.lower,115744026843262+c.upper)) = pointBounds69601 := by
 decide +kernel
def cuts69602 : List PrefixCut := [⟨64,175789366,175789468⟩]
theorem checked69602 : checkPrefixCuts (2^48) 9126805505 10 Manual.Count131072.C069602.packed 64 cuts69602 = true := by
 decide +kernel
def cuts69603 : List PrefixCut := [⟨26,72288796,72288837⟩,
⟨64,176989605,176989714⟩]
theorem checked69603 : checkPrefixCuts (2^48) 9126936577 10 Manual.Count131072.C069603.packed 64 cuts69603 = true := by
 decide +kernel
def pointBounds69603 : List (Nat × Nat × Nat) := [(9126989824,115744061526888,115744450991122)]
theorem point_links_checked69603 : (cuts69603.take 1).map (fun c => (9126936577-1+2*2^10*c.k,115743989238092+c.lower,115744378702285+c.upper)) = pointBounds69603 := by
 decide +kernel
def cuts69604 : List PrefixCut := [⟨64,175876849,175876953⟩]
theorem checked69604 : checkPrefixCuts (2^48) 9127067649 10 Manual.Count131072.C069604.packed 64 cuts69604 = true := by
 decide +kernel
def cuts69605 : List PrefixCut := [⟨38,103248974,103249033⟩,
⟨64,175781787,175781886⟩]
theorem checked69605 : checkPrefixCuts (2^48) 9127198721 10 Manual.Count131072.C069605.packed 64 cuts69605 = true := by
 decide +kernel
def pointBounds69605 : List (Nat × Nat × Nat) := [(9127276544,115744445353520,115744834817985)]
theorem point_links_checked69605 : (cuts69605.take 1).map (fun c => (9127198721-1+2*2^10*c.k,115744342104546+c.lower,115744731568952+c.upper)) = pointBounds69605 := by
 decide +kernel
def cuts69606 : List PrefixCut := [⟨64,178462223,178462325⟩]
theorem checked69606 : checkPrefixCuts (2^48) 9127329793 10 Manual.Count131072.C069606.packed 64 cuts69606 = true := by
 decide +kernel
def cuts69607 : List PrefixCut := [⟨50,136242616,136242694⟩,
⟨64,175375852,175375949⟩]
theorem checked69607 : checkPrefixCuts (2^48) 9127460865 10 Manual.Count131072.C069607.packed 64 cuts69607 = true := by
 decide +kernel
def pointBounds69607 : List (Nat × Nat × Nat) := [(9127563264,115744832591172,115745222055857)]
theorem point_links_checked69607 : (cuts69607.take 1).map (fun c => (9127460865-1+2*2^10*c.k,115744696348556+c.lower,115745085813163+c.upper)) = pointBounds69607 := by
 decide +kernel
def cuts69608 : List PrefixCut := [⟨64,177069411,177069519⟩]
theorem checked69608 : checkPrefixCuts (2^48) 9127591937 10 Manual.Count131072.C069608.packed 64 cuts69608 = true := by
 decide +kernel
def cuts69609 : List PrefixCut := [⟨62,169604303,169604401⟩,
⟨64,175648340,175648442⟩]
theorem checked69609 : checkPrefixCuts (2^48) 9127723009 10 Manual.Count131072.C069609.packed 64 cuts69609 = true := by
 decide +kernel
def pointBounds69609 : List (Nat × Nat × Nat) := [(9127849984,115745218398122,115745607863032)]
theorem point_links_checked69609 : (cuts69609.take 1).map (fun c => (9127723009-1+2*2^10*c.k,115745048793819+c.lower,115745438258631+c.upper)) = pointBounds69609 := by
 decide +kernel
def cuts69610 : List PrefixCut := [⟨64,178482797,178482903⟩]
theorem checked69610 : checkPrefixCuts (2^48) 9127854081 10 Manual.Count131072.C069610.packed 64 cuts69610 = true := by
 decide +kernel
def cuts69611 : List PrefixCut := [⟨64,176506716,176506818⟩]
theorem checked69611 : checkPrefixCuts (2^48) 9127985153 10 Manual.Count131072.C069611.packed 64 cuts69611 = true := by
 decide +kernel
def cuts69612 : List PrefixCut := [⟨10,25994747,25994763⟩,
⟨64,174438176,174438282⟩]
theorem checked69612 : checkPrefixCuts (2^48) 9128116225 10 Manual.Count131072.C069612.packed 64 cuts69612 = true := by
 decide +kernel
def pointBounds69612 : List (Nat × Nat × Nat) := [(9128136704,115745605426419,115745994891557)]
theorem point_links_checked69612 : (cuts69612.take 1).map (fun c => (9128116225-1+2*2^10*c.k,115745579431672+c.lower,115745968896794+c.upper)) = pointBounds69612 := by
 decide +kernel
def cuts69613 : List PrefixCut := [⟨64,176779171,176779276⟩]
theorem checked69613 : checkPrefixCuts (2^48) 9128247297 10 Manual.Count131072.C069613.packed 64 cuts69613 = true := by
 decide +kernel
def cuts69614 : List PrefixCut := [⟨22,60128390,60128426⟩,
⟨64,175234884,175234988⟩]
theorem checked69614 : checkPrefixCuts (2^48) 9128378369 10 Manual.Count131072.C069614.packed 64 cuts69614 = true := by
 decide +kernel
def pointBounds69614 : List (Nat × Nat × Nat) := [(9128423424,115745990777409,115746380242778)]
theorem point_links_checked69614 : (cuts69614.take 1).map (fun c => (9128378369-1+2*2^10*c.k,115745930649019+c.lower,115746320114352+c.upper)) = pointBounds69614 := by
 decide +kernel
def cuts69615 : List PrefixCut := [⟨64,175725710,175725816⟩]
theorem checked69615 : checkPrefixCuts (2^48) 9128509441 10 Manual.Count131072.C069615.packed 64 cuts69615 = true := by
 decide +kernel
def cuts69616 : List PrefixCut := [⟨34,93643288,93643345⟩,
⟨64,175353177,175353282⟩]
theorem checked69616 : checkPrefixCuts (2^48) 9128640513 10 Manual.Count131072.C069616.packed 64 cuts69616 = true := by
 decide +kernel
def pointBounds69616 : List (Nat × Nat × Nat) := [(9128710144,115746375252901,115746764718501)]
theorem point_links_checked69616 : (cuts69616.take 1).map (fun c => (9128640513-1+2*2^10*c.k,115746281609613+c.lower,115746671075156+c.upper)) = pointBounds69616 := by
 decide +kernel
def cuts69617 : List PrefixCut := [⟨64,176244828,176244927⟩]
theorem checked69617 : checkPrefixCuts (2^48) 9128771585 10 Manual.Count131072.C069617.packed 64 cuts69617 = true := by
 decide +kernel
def cuts69618 : List PrefixCut := [⟨46,125768686,125768760⟩,
⟨64,174854815,174854917⟩]
theorem checked69618 : checkPrefixCuts (2^48) 9128902657 10 Manual.Count131072.C069618.packed 64 cuts69618 = true := by
 decide +kernel
def pointBounds69618 : List (Nat × Nat × Nat) := [(9128996864,115746758976304,115747148442125)]
theorem point_links_checked69618 : (cuts69618.take 1).map (fun c => (9128902657-1+2*2^10*c.k,115746633207618+c.lower,115747022673365+c.upper)) = pointBounds69618 := by
 decide +kernel
def cuts69619 : List PrefixCut := [⟨64,174328151,174328250⟩]
theorem checked69619 : checkPrefixCuts (2^48) 9129033729 10 Manual.Count131072.C069619.packed 64 cuts69619 = true := by
 decide +kernel
def cuts69620 : List PrefixCut := [⟨58,161006225,161006318⟩,
⟨64,177933032,177933134⟩]
theorem checked69620 : checkPrefixCuts (2^48) 9129164801 10 Manual.Count131072.C069620.packed 64 cuts69620 = true := by
 decide +kernel
def pointBounds69620 : List (Nat × Nat × Nat) := [(9129283584,115747143396809,115747532862850)]
theorem point_links_checked69620 : (cuts69620.take 1).map (fun c => (9129164801-1+2*2^10*c.k,115746982390584+c.lower,115747371856532+c.upper)) = pointBounds69620 := by
 decide +kernel
def cuts69621 : List PrefixCut := [⟨64,174662292,174662391⟩]
theorem checked69621 : checkPrefixCuts (2^48) 9129295873 10 Manual.Count131072.C069621.packed 64 cuts69621 = true := by
 decide +kernel
def cuts69622 : List PrefixCut := [⟨64,174752296,174752396⟩]
theorem checked69622 : checkPrefixCuts (2^48) 9129426945 10 Manual.Count131072.C069622.packed 64 cuts69622 = true := by
 decide +kernel
def cuts69623 : List PrefixCut := [⟨6,16987960,16987970⟩,
⟨64,175890527,175890626⟩]
theorem checked69623 : checkPrefixCuts (2^48) 9129558017 10 Manual.Count131072.C069623.packed 64 cuts69623 = true := by
 decide +kernel
def pointBounds69623 : List (Nat × Nat × Nat) := [(9129570304,115747526726164,115747916192423)]
theorem point_links_checked69623 : (cuts69623.take 1).map (fun c => (9129558017-1+2*2^10*c.k,115747509738204+c.lower,115747899204453+c.upper)) = pointBounds69623 := by
 decide +kernel
def cuts69624 : List PrefixCut := [⟨64,175271391,175271486⟩]
theorem checked69624 : checkPrefixCuts (2^48) 9129689089 10 Manual.Count131072.C069624.packed 64 cuts69624 = true := by
 decide +kernel
def cuts69625 : List PrefixCut := [⟨18,48095137,48095167⟩,
⟨64,175176370,175176474⟩]
theorem checked69625 : checkPrefixCuts (2^48) 9129820161 10 Manual.Count131072.C069625.packed 64 cuts69625 = true := by
 decide +kernel
def pointBounds69625 : List (Nat × Nat × Nat) := [(9129857024,115747908995259,115748298461732)]
theorem point_links_checked69625 : (cuts69625.take 1).map (fun c => (9129820161-1+2*2^10*c.k,115747860900122+c.lower,115748250366565+c.upper)) = pointBounds69625 := by
 decide +kernel
def cuts69626 : List PrefixCut := [⟨64,174495613,174495719⟩]
theorem checked69626 : checkPrefixCuts (2^48) 9129951233 10 Manual.Count131072.C069626.packed 64 cuts69626 = true := by
 decide +kernel
def cuts69627 : List PrefixCut := [⟨30,81820934,81820982⟩,
⟨64,176990259,176990367⟩]
theorem checked69627 : checkPrefixCuts (2^48) 9130082305 10 Manual.Count131072.C069627.packed 64 cuts69627 = true := by
 decide +kernel
def pointBounds69627 : List (Nat × Nat × Nat) := [(9130143744,115748292393039,115748681859740)]
theorem point_links_checked69627 : (cuts69627.take 1).map (fun c => (9130082305-1+2*2^10*c.k,115748210572105+c.lower,115748600038758+c.upper)) = pointBounds69627 := by
 decide +kernel
def cuts69628 : List PrefixCut := [⟨64,176124536,176124636⟩]
theorem checked69628 : checkPrefixCuts (2^48) 9130213377 10 Manual.Count131072.C069628.packed 64 cuts69628 = true := by
 decide +kernel
def cuts69629 : List PrefixCut := [⟨42,116284582,116284651⟩,
⟨64,176861883,176861985⟩]
theorem checked69629 : checkPrefixCuts (2^48) 9130344449 10 Manual.Count131072.C069629.packed 64 cuts69629 = true := by
 decide +kernel
def pointBounds69629 : List (Nat × Nat × Nat) := [(9130430464,115748679971482,115749069438412)]
theorem point_links_checked69629 : (cuts69629.take 1).map (fun c => (9130344449-1+2*2^10*c.k,115748563686900+c.lower,115748953153761+c.upper)) = pointBounds69629 := by
 decide +kernel
def cuts69630 : List PrefixCut := [⟨64,175965324,175965428⟩]
theorem checked69630 : checkPrefixCuts (2^48) 9130475521 10 Manual.Count131072.C069630.packed 64 cuts69630 = true := by
 decide +kernel
def cuts69631 : List PrefixCut := [⟨54,149019822,149019905⟩,
⟨64,176887626,176887724⟩]
theorem checked69631 : checkPrefixCuts (2^48) 9130606593 10 Manual.Count131072.C069631.packed 64 cuts69631 = true := by
 decide +kernel
def pointBounds69631 : List (Nat × Nat × Nat) := [(9130717184,115749065533929,115749455001079)]
theorem point_links_checked69631 : (cuts69631.take 1).map (fun c => (9130606593-1+2*2^10*c.k,115748916514107+c.lower,115749305981174+c.upper)) = pointBounds69631 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000300
