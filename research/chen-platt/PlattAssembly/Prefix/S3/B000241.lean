import PlattAssemblyKernel
import PlattCertificates.Count131072.C027712
import PlattCertificates.Count131072.C027713
import PlattCertificates.Count131072.C027714
import PlattCertificates.Count131072.C027715
import PlattCertificates.Count131072.C027716
import PlattCertificates.Count131072.C027717
import PlattCertificates.Count131072.C027718
import PlattCertificates.Count131072.C027719
import PlattCertificates.Count131072.C027720
import PlattCertificates.Count131072.C027721
import PlattCertificates.Count131072.C027722
import PlattCertificates.Count131072.C027723
import PlattCertificates.Count131072.C027724
import PlattCertificates.Count131072.C027725
import PlattCertificates.Count131072.C027726
import PlattCertificates.Count131072.C027727
import PlattCertificates.Count131072.C027728
import PlattCertificates.Count131072.C027729
import PlattCertificates.Count131072.C027730
import PlattCertificates.Count131072.C027731
import PlattCertificates.Count131072.C027732
import PlattCertificates.Count131072.C027733
import PlattCertificates.Count131072.C027734
import PlattCertificates.Count131072.C027735
import PlattCertificates.Count131072.C027736
import PlattCertificates.Count131072.C027737
import PlattCertificates.Count131072.C027738
import PlattCertificates.Count131072.C027739
import PlattCertificates.Count131072.C027740
import PlattCertificates.Count131072.C027741
import PlattCertificates.Count131072.C027742
import PlattCertificates.Count131072.C027743
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000241
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts27712 : List PrefixCut := [⟨6,20823030,20823041⟩,
⟨117,420788895,420789134⟩,
⟨128,460033950,460034212⟩]
theorem checked27712 : checkPrefixCuts (2^48) 3636199425 9 Manual.Count131072.C027712.packed 128 cuts27712 = true := by
 decide +kernel
def pointBounds27712 : List (Nat × Nat × Nat) := [(3636205568,104216512748513,104216895503092),(3636319232,104216912714378,104217295469185)]
theorem point_links_checked27712 : (cuts27712.take 2).map (fun c => (3636199425-1+2*2^9*c.k,104216491925483+c.lower,104216874680051+c.upper)) = pointBounds27712 := by
 decide +kernel
def cuts27713 : List PrefixCut := [⟨100,359701999,359702201⟩,
⟨128,457076003,457076261⟩]
theorem checked27713 : checkPrefixCuts (2^48) 3636330497 9 Manual.Count131072.C027713.packed 128 cuts27713 = true := by
 decide +kernel
def pointBounds27713 : List (Nat × Nat × Nat) := [(3636432896,104217311661432,104217694416464)]
theorem point_links_checked27713 : (cuts27713.take 1).map (fun c => (3636330497-1+2*2^9*c.k,104216951959433+c.lower,104217334714263+c.upper)) = pointBounds27713 := by
 decide +kernel
def cuts27714 : List PrefixCut := [⟨83,295677942,295678105⟩,
⟨128,453499009,453499261⟩]
theorem checked27714 : checkPrefixCuts (2^48) 3636461569 9 Manual.Count131072.C027714.packed 128 cuts27714 = true := by
 decide +kernel
def pointBounds27714 : List (Nat × Nat × Nat) := [(3636546560,104217704713378,104218087468629)]
theorem point_links_checked27714 : (cuts27714.take 1).map (fun c => (3636461569-1+2*2^9*c.k,104217409035436+c.lower,104217791790524+c.upper)) = pointBounds27714 := by
 decide +kernel
def cuts27715 : List PrefixCut := [⟨66,241333224,241333355⟩,
⟨128,462770639,462770894⟩]
theorem checked27715 : checkPrefixCuts (2^48) 3636592641 9 Manual.Count131072.C027715.packed 128 cuts27715 = true := by
 decide +kernel
def pointBounds27715 : List (Nat × Nat × Nat) := [(3636660224,104218103867669,104218486623140)]
theorem point_links_checked27715 : (cuts27715.take 1).map (fun c => (3636592641-1+2*2^9*c.k,104217862534445+c.lower,104218245289785+c.upper)) = pointBounds27715 := by
 decide +kernel
def cuts27716 : List PrefixCut := [⟨49,181032520,181032619⟩,
⟨128,470261388,470261647⟩]
theorem checked27716 : checkPrefixCuts (2^48) 3636723713 9 Manual.Count131072.C027716.packed 128 cuts27716 = true := by
 decide +kernel
def pointBounds27716 : List (Nat × Nat × Nat) := [(3636773888,104218506337604,104218889093298)]
theorem point_links_checked27716 : (cuts27716.take 1).map (fun c => (3636723713-1+2*2^9*c.k,104218325305084+c.lower,104218708060679+c.upper)) = pointBounds27716 := by
 decide +kernel
def cuts27717 : List PrefixCut := [⟨32,111835464,111835527⟩,
⟨128,456158735,456158994⟩]
theorem checked27717 : checkPrefixCuts (2^48) 3636854785 9 Manual.Count131072.C027717.packed 128 cuts27717 = true := by
 decide +kernel
def pointBounds27717 : List (Nat × Nat × Nat) := [(3636887552,104218907401936,104219290157853)]
theorem point_links_checked27717 : (cuts27717.take 1).map (fun c => (3636854785-1+2*2^9*c.k,104218795566472+c.lower,104219178322326+c.upper)) = pointBounds27717 := by
 decide +kernel
def cuts27718 : List PrefixCut := [⟨15,54716284,54716312⟩,
⟨126,448403388,448403637⟩,
⟨128,454981503,454981755⟩]
theorem checked27718 : checkPrefixCuts (2^48) 3636985857 9 Manual.Count131072.C027718.packed 128 cuts27718 = true := by
 decide +kernel
def pointBounds27718 : List (Nat × Nat × Nat) := [(3637001216,104219306441491,104219689197632),(3637114880,104219700128595,104220082884957)]
theorem point_links_checked27718 : (cuts27718.take 2).map (fun c => (3636985857-1+2*2^9*c.k,104219251725207+c.lower,104219634481320+c.upper)) = pointBounds27718 := by
 decide +kernel
def cuts27719 : List PrefixCut := [⟨109,391275644,391275865⟩,
⟨128,460382219,460382478⟩]
theorem checked27719 : checkPrefixCuts (2^48) 3637116929 9 Manual.Count131072.C027719.packed 128 cuts27719 = true := by
 decide +kernel
def pointBounds27719 : List (Nat × Nat × Nat) := [(3637228544,104220097982354,104220480738940)]
theorem point_links_checked27719 : (cuts27719.take 1).map (fun c => (3637116929-1+2*2^9*c.k,104219706706710+c.lower,104220089463075+c.upper)) = pointBounds27719 := by
 decide +kernel
def cuts27720 : List PrefixCut := [⟨92,332913615,332913801⟩,
⟨128,462222918,462223178⟩]
theorem checked27720 : checkPrefixCuts (2^48) 3637248001 9 Manual.Count131072.C027720.packed 128 cuts27720 = true := by
 decide +kernel
def pointBounds27720 : List (Nat × Nat × Nat) := [(3637342208,104220500002544,104220882759354)]
theorem point_links_checked27720 : (cuts27720.take 1).map (fun c => (3637248001-1+2*2^9*c.k,104220167088929+c.lower,104220549845553+c.upper)) = pointBounds27720 := by
 decide +kernel
def cuts27721 : List PrefixCut := [⟨76,270763702,270763851⟩,
⟨128,457331145,457331395⟩]
theorem checked27721 : checkPrefixCuts (2^48) 3637379073 9 Manual.Count131072.C027721.packed 128 cuts27721 = true := by
 decide +kernel
def pointBounds27721 : List (Nat × Nat × Nat) := [(3637456896,104220900075549,104221282832582)]
theorem point_links_checked27721 : (cuts27721.take 1).map (fun c => (3637379073-1+2*2^9*c.k,104220629311847+c.lower,104221012068731+c.upper)) = pointBounds27721 := by
 decide +kernel
def cuts27722 : List PrefixCut := [⟨60,214498891,214499010⟩,
⟨128,467992978,467993237⟩]
theorem checked27722 : checkPrefixCuts (2^48) 3637510145 9 Manual.Count131072.C027722.packed 128 cuts27722 = true := by
 decide +kernel
def pointBounds27722 : List (Nat × Nat × Nat) := [(3637571584,104221301141883,104221683899136)]
theorem point_links_checked27722 : (cuts27722.take 1).map (fun c => (3637510145-1+2*2^9*c.k,104221086642992+c.lower,104221469400126+c.upper)) = pointBounds27722 := by
 decide +kernel
def cuts27723 : List PrefixCut := [⟨44,156999818,156999908⟩,
⟨128,456756524,456756781⟩]
theorem checked27723 : checkPrefixCuts (2^48) 3637641217 9 Manual.Count131072.C027723.packed 128 cuts27723 = true := by
 decide +kernel
def pointBounds27723 : List (Nat × Nat × Nat) := [(3637686272,104221711635788,104222094393271)]
theorem point_links_checked27723 : (cuts27723.take 1).map (fun c => (3637641217-1+2*2^9*c.k,104221554635970+c.lower,104221937393363+c.upper)) = pointBounds27723 := by
 decide +kernel
def cuts27724 : List PrefixCut := [⟨28,100123658,100123716⟩,
⟨128,462775272,462775532⟩]
theorem checked27724 : checkPrefixCuts (2^48) 3637772289 9 Manual.Count131072.C027724.packed 128 cuts27724 = true := by
 decide +kernel
def pointBounds27724 : List (Nat × Nat × Nat) := [(3637800960,104222111516152,104222494273860)]
theorem point_links_checked27724 : (cuts27724.take 1).map (fun c => (3637772289-1+2*2^9*c.k,104222011392494+c.lower,104222394150144+c.upper)) = pointBounds27724 := by
 decide +kernel
def cuts27725 : List PrefixCut := [⟨12,43173969,43173993⟩,
⟨124,445272911,445273156⟩,
⟨128,459663748,459664001⟩]
theorem checked27725 : checkPrefixCuts (2^48) 3637903361 9 Manual.Count131072.C027725.packed 128 cuts27725 = true := by
 decide +kernel
def pointBounds27725 : List (Nat × Nat × Nat) := [(3637915648,104222517341735,104222900099669),(3638030336,104222919440677,104223302198832)]
theorem point_links_checked27725 : (cuts27725.take 2).map (fun c => (3637903361-1+2*2^9*c.k,104222474167766+c.lower,104222856925676+c.upper)) = pointBounds27725 := by
 decide +kernel
def cuts27726 : List PrefixCut := [⟨108,390635440,390635658⟩,
⟨128,461271945,461272205⟩]
theorem checked27726 : checkPrefixCuts (2^48) 3638034433 9 Manual.Count131072.C027726.packed 128 cuts27726 = true := by
 decide +kernel
def pointBounds27726 : List (Nat × Nat × Nat) := [(3638145024,104223324466954,104223707225335)]
theorem point_links_checked27726 : (cuts27726.take 1).map (fun c => (3638034433-1+2*2^9*c.k,104222933831514+c.lower,104223316589677+c.upper)) = pointBounds27726 := by
 decide +kernel
def cuts27727 : List PrefixCut := [⟨92,338013189,338013374⟩,
⟨128,468063534,468063790⟩]
theorem checked27727 : checkPrefixCuts (2^48) 3638165505 9 Manual.Count131072.C027727.packed 128 cuts27727 = true := by
 decide +kernel
def pointBounds27727 : List (Nat × Nat × Nat) := [(3638259712,104223733116648,104224115875256)]
theorem point_links_checked27727 : (cuts27727.take 1).map (fun c => (3638165505-1+2*2^9*c.k,104223395103459+c.lower,104223777861882+c.upper)) = pointBounds27727 := by
 decide +kernel
def cuts27728 : List PrefixCut := [⟨76,270385933,270386087⟩,
⟨128,461625429,461625687⟩]
theorem checked27728 : checkPrefixCuts (2^48) 3638296577 9 Manual.Count131072.C027728.packed 128 cuts27728 = true := by
 decide +kernel
def pointBounds27728 : List (Nat × Nat × Nat) := [(3638374400,104224133552926,104224516311759)]
theorem point_links_checked27728 : (cuts27728.take 1).map (fun c => (3638296577-1+2*2^9*c.k,104223863166993+c.lower,104224245925672+c.upper)) = pointBounds27728 := by
 decide +kernel
def cuts27729 : List PrefixCut := [⟨60,219550601,219550723⟩,
⟨128,467024099,467024360⟩]
theorem checked27729 : checkPrefixCuts (2^48) 3638427649 9 Manual.Count131072.C027729.packed 128 cuts27729 = true := by
 decide +kernel
def pointBounds27729 : List (Nat × Nat × Nat) := [(3638489088,104224544343023,104224927102082)]
theorem point_links_checked27729 : (cuts27729.take 1).map (fun c => (3638427649-1+2*2^9*c.k,104224324792422+c.lower,104224707551359+c.upper)) = pointBounds27729 := by
 decide +kernel
def cuts27730 : List PrefixCut := [⟨44,156728157,156728245⟩,
⟨128,453237606,453237862⟩]
theorem checked27730 : checkPrefixCuts (2^48) 3638558721 9 Manual.Count131072.C027730.packed 128 cuts27730 = true := by
 decide +kernel
def pointBounds27730 : List (Nat × Nat × Nat) := [(3638603776,104224948544678,104225331303964)]
theorem point_links_checked27730 : (cuts27730.take 1).map (fun c => (3638558721-1+2*2^9*c.k,104224791816521+c.lower,104225174575719+c.upper)) = pointBounds27730 := by
 decide +kernel
def cuts27731 : List PrefixCut := [⟨28,101181404,101181460⟩,
⟨128,458790891,458791146⟩]
theorem checked27731 : checkPrefixCuts (2^48) 3638689793 9 Manual.Count131072.C027731.packed 128 cuts27731 = true := by
 decide +kernel
def pointBounds27731 : List (Nat × Nat × Nat) := [(3638718464,104225346235531,104225728995041)]
theorem point_links_checked27731 : (cuts27731.take 1).map (fun c => (3638689793-1+2*2^9*c.k,104225245054127+c.lower,104225627813581+c.upper)) = pointBounds27731 := by
 decide +kernel
def cuts27732 : List PrefixCut := [⟨12,41616019,41616042⟩,
⟨124,449105540,449105788⟩,
⟨128,464420956,464421212⟩]
theorem checked27732 : checkPrefixCuts (2^48) 3638820865 9 Manual.Count131072.C027732.packed 128 cuts27732 = true := by
 decide +kernel
def pointBounds27732 : List (Nat × Nat × Nat) := [(3638833152,104225745461037,104226128220769),(3638947840,104226152950558,104226535710515)]
theorem point_links_checked27732 : (cuts27732.take 2).map (fun c => (3638820865-1+2*2^9*c.k,104225703845018+c.lower,104226086604727+c.upper)) = pointBounds27732 := by
 decide +kernel
def cuts27733 : List PrefixCut := [⟨108,385199832,385200051⟩,
⟨128,457829582,457829840⟩]
theorem checked27733 : checkPrefixCuts (2^48) 3638951937 9 Manual.Count131072.C027733.packed 128 cuts27733 = true := by
 decide +kernel
def pointBounds27733 : List (Nat × Nat × Nat) := [(3639062528,104226553465806,104226936225990)]
theorem point_links_checked27733 : (cuts27733.take 1).map (fun c => (3638951937-1+2*2^9*c.k,104226168265974+c.lower,104226551025939+c.upper)) = pointBounds27733 := by
 decide +kernel
def cuts27734 : List PrefixCut := [⟨92,329187779,329187966⟩,
⟨128,463304644,463304905⟩]
theorem checked27734 : checkPrefixCuts (2^48) 3639083009 9 Manual.Count131072.C027734.packed 128 cuts27734 = true := by
 decide +kernel
def pointBounds27734 : List (Nat × Nat × Nat) := [(3639177216,104226955283335,104227338043745)]
theorem point_links_checked27734 : (cuts27734.take 1).map (fun c => (3639083009-1+2*2^9*c.k,104226626095556+c.lower,104227008855779+c.upper)) = pointBounds27734 := by
 decide +kernel
def cuts27735 : List PrefixCut := [⟨76,270008429,270008578⟩,
⟨128,459266115,459266370⟩]
theorem checked27735 : checkPrefixCuts (2^48) 3639214081 9 Manual.Count131072.C027735.packed 128 cuts27735 = true := by
 decide +kernel
def pointBounds27735 : List (Nat × Nat × Nat) := [(3639291904,104227359408629,104227742169262)]
theorem point_links_checked27735 : (cuts27735.take 1).map (fun c => (3639214081-1+2*2^9*c.k,104227089400200+c.lower,104227472160684+c.upper)) = pointBounds27735 := by
 decide +kernel
def cuts27736 : List PrefixCut := [⟨60,213230576,213230697⟩,
⟨128,464276670,464276929⟩]
theorem checked27736 : checkPrefixCuts (2^48) 3639345153 9 Manual.Count131072.C027736.packed 128 cuts27736 = true := by
 decide +kernel
def pointBounds27736 : List (Nat × Nat × Nat) := [(3639406592,104227761896891,104228144657751)]
theorem point_links_checked27736 : (cuts27736.take 1).map (fun c => (3639345153-1+2*2^9*c.k,104227548666315+c.lower,104227931427054+c.upper)) = pointBounds27736 := by
 decide +kernel
def cuts27737 : List PrefixCut := [⟨44,158622115,158622201⟩,
⟨128,457299686,457299943⟩]
theorem checked27737 : checkPrefixCuts (2^48) 3639476225 9 Manual.Count131072.C027737.packed 128 cuts27737 = true := by
 decide +kernel
def pointBounds27737 : List (Nat × Nat × Nat) := [(3639521280,104228171565100,104228554326184)]
theorem point_links_checked27737 : (cuts27737.take 1).map (fun c => (3639476225-1+2*2^9*c.k,104228012942985+c.lower,104228395703983+c.upper)) = pointBounds27737 := by
 decide +kernel
def cuts27738 : List PrefixCut := [⟨28,101001208,101001265⟩,
⟨128,462541925,462542187⟩]
theorem checked27738 : checkPrefixCuts (2^48) 3639607297 9 Manual.Count131072.C027738.packed 128 cuts27738 = true := by
 decide +kernel
def pointBounds27738 : List (Nat × Nat × Nat) := [(3639635968,104228571243879,104228954005191)]
theorem point_links_checked27738 : (cuts27738.take 1).map (fun c => (3639607297-1+2*2^9*c.k,104228470242671+c.lower,104228853003926+c.upper)) = pointBounds27738 := by
 decide +kernel
def cuts27739 : List PrefixCut := [⟨12,43848205,43848231⟩,
⟨124,446981806,446982054⟩,
⟨128,460437415,460437671⟩]
theorem checked27739 : checkPrefixCuts (2^48) 3639738369 9 Manual.Count131072.C027739.packed 128 cuts27739 = true := by
 decide +kernel
def pointBounds27739 : List (Nat × Nat × Nat) := [(3639750656,104228976632801,104229359394344),(3639865344,104229379766402,104229762528167)]
theorem point_links_checked27739 : (cuts27739.take 2).map (fun c => (3639738369-1+2*2^9*c.k,104228932784596+c.lower,104229315546113+c.upper)) = pointBounds27739 := by
 decide +kernel
def cuts27740 : List PrefixCut := [⟨108,387267970,387268190⟩,
⟨128,460575364,460575625⟩]
theorem checked27740 : checkPrefixCuts (2^48) 3639869441 9 Manual.Count131072.C027740.packed 128 cuts27740 = true := by
 decide +kernel
def pointBounds27740 : List (Nat × Nat × Nat) := [(3639980032,104229780489981,104230163251974)]
theorem point_links_checked27740 : (cuts27740.take 1).map (fun c => (3639869441-1+2*2^9*c.k,104229393222011+c.lower,104229775983784+c.upper)) = pointBounds27740 := by
 decide +kernel
def cuts27741 : List PrefixCut := [⟨92,331269946,331270128⟩,
⟨128,460017504,460017759⟩]
theorem checked27741 : checkPrefixCuts (2^48) 3640000513 9 Manual.Count131072.C027741.packed 128 cuts27741 = true := by
 decide +kernel
def pointBounds27741 : List (Nat × Nat × Nat) := [(3640094720,104230185067321,104230567829537)]
theorem point_links_checked27741 : (cuts27741.take 1).map (fun c => (3640000513-1+2*2^9*c.k,104229853797375+c.lower,104230236559409+c.upper)) = pointBounds27741 := by
 decide +kernel
def cuts27742 : List PrefixCut := [⟨76,275739700,275739853⟩,
⟨128,463480559,463480818⟩]
theorem checked27742 : checkPrefixCuts (2^48) 3640131585 9 Manual.Count131072.C027742.packed 128 cuts27742 = true := by
 decide +kernel
def pointBounds27742 : List (Nat × Nat × Nat) := [(3640209408,104230589554579,104230972317021)]
theorem point_links_checked27742 : (cuts27742.take 1).map (fun c => (3640131585-1+2*2^9*c.k,104230313814879+c.lower,104230696577168+c.upper)) = pointBounds27742 := by
 decide +kernel
def cuts27743 : List PrefixCut := [⟨60,211862380,211862504⟩,
⟨128,461839999,461840264⟩]
theorem checked27743 : checkPrefixCuts (2^48) 3640262657 9 Manual.Count131072.C027743.packed 128 cuts27743 = true := by
 decide +kernel
def pointBounds27743 : List (Nat × Nat × Nat) := [(3640324096,104230989157818,104231371920490)]
theorem point_links_checked27743 : (cuts27743.take 1).map (fun c => (3640262657-1+2*2^9*c.k,104230777295438+c.lower,104231160057986+c.upper)) = pointBounds27743 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000241
