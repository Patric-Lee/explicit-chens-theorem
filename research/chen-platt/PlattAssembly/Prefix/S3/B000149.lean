import PlattAssemblyKernel
import PlattCertificates.Count131072.C024768
import PlattCertificates.Count131072.C024769
import PlattCertificates.Count131072.C024770
import PlattCertificates.Count131072.C024771
import PlattCertificates.Count131072.C024772
import PlattCertificates.Count131072.C024773
import PlattCertificates.Count131072.C024774
import PlattCertificates.Count131072.C024775
import PlattCertificates.Count131072.C024776
import PlattCertificates.Count131072.C024777
import PlattCertificates.Count131072.C024778
import PlattCertificates.Count131072.C024779
import PlattCertificates.Count131072.C024780
import PlattCertificates.Count131072.C024781
import PlattCertificates.Count131072.C024782
import PlattCertificates.Count131072.C024783
import PlattCertificates.Count131072.C024784
import PlattCertificates.Count131072.C024785
import PlattCertificates.Count131072.C024786
import PlattCertificates.Count131072.C024787
import PlattCertificates.Count131072.C024788
import PlattCertificates.Count131072.C024789
import PlattCertificates.Count131072.C024790
import PlattCertificates.Count131072.C024791
import PlattCertificates.Count131072.C024792
import PlattCertificates.Count131072.C024793
import PlattCertificates.Count131072.C024794
import PlattCertificates.Count131072.C024795
import PlattCertificates.Count131072.C024796
import PlattCertificates.Count131072.C024797
import PlattCertificates.Count131072.C024798
import PlattCertificates.Count131072.C024799
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000149
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts24768 : List PrefixCut := [⟨19,79324487,79324532⟩,
⟨119,484859056,484859329⟩,
⟨128,520276687,520276980⟩]
theorem checked24768 : checkPrefixCuts (2^48) 3250323457 9 Manual.Count131072.C024768.packed 128 cuts24768 = true := by
 decide +kernel
def pointBounds24768 : List (Nat × Nat × Nat) := [(3250342912,102778456353950,102778838303294),(3250445312,102778861888519,102779243838091)]
theorem point_links_checked24768 : (cuts24768.take 2).map (fun c => (3250323457-1+2*2^9*c.k,102778377029463+c.lower,102778758978762+c.upper)) = pointBounds24768 := by
 decide +kernel
def cuts24769 : List PrefixCut := [⟨91,358846800,358846999⟩,
⟨128,516185495,516185779⟩]
theorem checked24769 : checkPrefixCuts (2^48) 3250454529 9 Manual.Count131072.C024769.packed 128 cuts24769 = true := by
 decide +kernel
def pointBounds24769 : List (Nat × Nat × Nat) := [(3250547712,102779256152950,102779638102741)]
theorem point_links_checked24769 : (cuts24769.take 1).map (fun c => (3250454529-1+2*2^9*c.k,102778897306150+c.lower,102779279255742+c.upper)) = pointBounds24769 := by
 decide +kernel
def cuts24770 : List PrefixCut := [⟨63,254751321,254751463⟩,
⟨128,517896630,517896918⟩]
theorem checked24770 : checkPrefixCuts (2^48) 3250585601 9 Manual.Count131072.C024770.packed 128 cuts24770 = true := by
 decide +kernel
def pointBounds24770 : List (Nat × Nat × Nat) := [(3250650112,102779668242966,102780050192984)]
theorem point_links_checked24770 : (cuts24770.take 1).map (fun c => (3250585601-1+2*2^9*c.k,102779413491645+c.lower,102779795441521+c.upper)) = pointBounds24770 := by
 decide +kernel
def cuts24771 : List PrefixCut := [⟨35,141744697,141744776⟩,
⟨128,511295179,511295461⟩]
theorem checked24771 : checkPrefixCuts (2^48) 3250716673 9 Manual.Count131072.C024771.packed 128 cuts24771 = true := by
 decide +kernel
def pointBounds24771 : List (Nat × Nat × Nat) := [(3250752512,102780073132972,102780455083215)]
theorem point_links_checked24771 : (cuts24771.take 1).map (fun c => (3250716673-1+2*2^9*c.k,102779931388275+c.lower,102780313338439+c.upper)) = pointBounds24771 := by
 decide +kernel
def cuts24772 : List PrefixCut := [⟨7,29612064,29612079⟩,
⟨107,435515595,435515834⟩,
⟨128,518720775,518721062⟩]
theorem checked24772 : checkPrefixCuts (2^48) 3250847745 9 Manual.Count131072.C024772.packed 128 cuts24772 = true := by
 decide +kernel
def pointBounds24772 : List (Nat × Nat × Nat) := [(3250854912,102780472295518,102780854245979),(3250957312,102780878199049,102781260149734)]
theorem point_links_checked24772 : (cuts24772.take 2).map (fun c => (3250847745-1+2*2^9*c.k,102780442683454+c.lower,102780824633900+c.upper)) = pointBounds24772 := by
 decide +kernel
def cuts24773 : List PrefixCut := [⟨79,317057768,317057953⟩,
⟨128,516794991,516795286⟩]
theorem checked24773 : checkPrefixCuts (2^48) 3250978817 9 Manual.Count131072.C024773.packed 128 cuts24773 = true := by
 decide +kernel
def pointBounds24773 : List (Nat × Nat × Nat) := [(3251059712,102781278461997,102781660412915)]
theorem point_links_checked24773 : (cuts24773.take 1).map (fun c => (3250978817-1+2*2^9*c.k,102780961404229+c.lower,102781343354962+c.upper)) = pointBounds24773 := by
 decide +kernel
def cuts24774 : List PrefixCut := [⟨51,209603889,209604008⟩,
⟨128,524479551,524479848⟩]
theorem checked24774 : checkPrefixCuts (2^48) 3251109889 9 Manual.Count131072.C024774.packed 128 cuts24774 = true := by
 decide +kernel
def pointBounds24774 : List (Nat × Nat × Nat) := [(3251162112,102781687803109,102782069754256)]
theorem point_links_checked24774 : (cuts24774.take 1).map (fun c => (3251109889-1+2*2^9*c.k,102781478199220+c.lower,102781860150248+c.upper)) = pointBounds24774 := by
 decide +kernel
def cuts24775 : List PrefixCut := [⟨23,88738649,88738699⟩,
⟨123,499439149,499439420⟩,
⟨128,518831093,518831377⟩]
theorem checked24775 : checkPrefixCuts (2^48) 3251240961 9 Manual.Count131072.C024775.packed 128 cuts24775 = true := by
 decide +kernel
def pointBounds24775 : List (Nat × Nat × Nat) := [(3251264512,102782091417420,102782473368795),(3251366912,102782502117920,102782884069516)]
theorem point_links_checked24775 : (cuts24775.take 2).map (fun c => (3251240961-1+2*2^9*c.k,102782002678771+c.lower,102782384630096+c.upper)) = pointBounds24775 := by
 decide +kernel
def cuts24776 : List PrefixCut := [⟨95,387919324,387919546⟩,
⟨128,525649127,525649428⟩]
theorem checked24776 : checkPrefixCuts (2^48) 3251372033 9 Manual.Count131072.C024776.packed 128 cuts24776 = true := by
 decide +kernel
def pointBounds24776 : List (Nat × Nat × Nat) := [(3251469312,102782909429188,102783291381019)]
theorem point_links_checked24776 : (cuts24776.take 1).map (fun c => (3251372033-1+2*2^9*c.k,102782521509864+c.lower,102782903461473+c.upper)) = pointBounds24776 := by
 decide +kernel
def cuts24777 : List PrefixCut := [⟨67,274243370,274243529⟩,
⟨128,521905744,521906042⟩]
theorem checked24777 : checkPrefixCuts (2^48) 3251503105 9 Manual.Count131072.C024777.packed 128 cuts24777 = true := by
 decide +kernel
def pointBounds24777 : List (Nat × Nat × Nat) := [(3251571712,102783321402361,102783703354430)]
theorem point_links_checked24777 : (cuts24777.take 1).map (fun c => (3251503105-1+2*2^9*c.k,102783047158991+c.lower,102783429110901+c.upper)) = pointBounds24777 := by
 decide +kernel
def cuts24778 : List PrefixCut := [⟨39,160748625,160748718⟩,
⟨128,526039630,526039918⟩]
theorem checked24778 : checkPrefixCuts (2^48) 3251634177 9 Manual.Count131072.C024778.packed 128 cuts24778 = true := by
 decide +kernel
def pointBounds24778 : List (Nat × Nat × Nat) := [(3251674112,102783729813360,102784111765661)]
theorem point_links_checked24778 : (cuts24778.take 1).map (fun c => (3251634177-1+2*2^9*c.k,102783569064735+c.lower,102783951016943+c.upper)) = pointBounds24778 := by
 decide +kernel
def cuts24779 : List PrefixCut := [⟨11,48127637,48127664⟩,
⟨111,442923156,442923399⟩,
⟨128,513467425,513467707⟩]
theorem checked24779 : checkPrefixCuts (2^48) 3251765249 9 Manual.Count131072.C024779.packed 128 cuts24779 = true := by
 decide +kernel
def pointBounds24779 : List (Nat × Nat × Nat) := [(3251776512,102784143232002,102784525184525),(3251878912,102784538027521,102784919980260)]
theorem point_links_checked24779 : (cuts24779.take 2).map (fun c => (3251765249-1+2*2^9*c.k,102784095104365+c.lower,102784477056861+c.upper)) = pointBounds24779 := by
 decide +kernel
def cuts24780 : List PrefixCut := [⟨83,338174340,338174523⟩,
⟨128,518986245,518986531⟩]
theorem checked24780 : checkPrefixCuts (2^48) 3251896321 9 Manual.Count131072.C024780.packed 128 cuts24780 = true := by
 decide +kernel
def pointBounds24780 : List (Nat × Nat × Nat) := [(3251981312,102784946746130,102785328699091)]
theorem point_links_checked24780 : (cuts24780.take 1).map (fun c => (3251896321-1+2*2^9*c.k,102784608571790+c.lower,102784990524568+c.upper)) = pointBounds24780 := by
 decide +kernel
def cuts24781 : List PrefixCut := [⟨55,222700645,222700769⟩,
⟨128,516888045,516888334⟩]
theorem checked24781 : checkPrefixCuts (2^48) 3252027393 9 Manual.Count131072.C024781.packed 128 cuts24781 = true := by
 decide +kernel
def pointBounds24781 : List (Nat × Nat × Nat) := [(3252083712,102785350258680,102785732211868)]
theorem point_links_checked24781 : (cuts24781.take 1).map (fun c => (3252027393-1+2*2^9*c.k,102785127558035+c.lower,102785509511099+c.upper)) = pointBounds24781 := by
 decide +kernel
def cuts24782 : List PrefixCut := [⟨27,110870307,110870366⟩,
⟨127,513751628,513751919⟩,
⟨128,518165510,518165803⟩]
theorem checked24782 : checkPrefixCuts (2^48) 3252158465 9 Manual.Count131072.C024782.packed 128 cuts24782 = true := by
 decide +kernel
def pointBounds24782 : List (Nat × Nat × Nat) := [(3252186112,102785755316387,102786137269799),(3252288512,102786158197708,102786540151352)]
theorem point_links_checked24782 : (cuts24782.take 2).map (fun c => (3252158465-1+2*2^9*c.k,102785644446080+c.lower,102786026399433+c.upper)) = pointBounds24782 := by
 decide +kernel
def cuts24783 : List PrefixCut := [⟨99,404512877,404513104⟩,
⟨128,519442771,519443062⟩]
theorem checked24783 : checkPrefixCuts (2^48) 3252289537 9 Manual.Count131072.C024783.packed 128 cuts24783 = true := by
 decide +kernel
def pointBounds24783 : List (Nat × Nat × Nat) := [(3252390912,102786567124467,102786949078340)]
theorem point_links_checked24783 : (cuts24783.take 1).map (fun c => (3252289537-1+2*2^9*c.k,102786162611590+c.lower,102786544565236+c.upper)) = pointBounds24783 := by
 decide +kernel
def cuts24784 : List PrefixCut := [⟨71,287579859,287580020⟩,
⟨128,517085229,517085518⟩]
theorem checked24784 : checkPrefixCuts (2^48) 3252420609 9 Manual.Count131072.C024784.packed 128 cuts24784 = true := by
 decide +kernel
def pointBounds24784 : List (Nat × Nat × Nat) := [(3252493312,102786969634220,102787351588318)]
theorem point_links_checked24784 : (cuts24784.take 1).map (fun c => (3252420609-1+2*2^9*c.k,102786682054361+c.lower,102787064008298+c.upper)) = pointBounds24784 := by
 decide +kernel
def cuts24785 : List PrefixCut := [⟨43,173943657,173943753⟩,
⟨128,525112357,525112643⟩]
theorem checked24785 : checkPrefixCuts (2^48) 3252551681 9 Manual.Count131072.C024785.packed 128 cuts24785 = true := by
 decide +kernel
def pointBounds24785 : List (Nat × Nat × Nat) := [(3252595712,102787373083247,102787755037569)]
theorem point_links_checked24785 : (cuts24785.take 1).map (fun c => (3252551681-1+2*2^9*c.k,102787199139590+c.lower,102787581093816+c.upper)) = pointBounds24785 := by
 decide +kernel
def cuts24786 : List PrefixCut := [⟨15,58238750,58238785⟩,
⟨115,462008484,462008740⟩,
⟨128,511245715,511246001⟩]
theorem checked24786 : checkPrefixCuts (2^48) 3252682753 9 Manual.Count131072.C024786.packed 128 cuts24786 = true := by
 decide +kernel
def pointBounds24786 : List (Nat × Nat × Nat) := [(3252698112,102787782490697,102788164445244),(3252800512,102788186260431,102788568215199)]
theorem point_links_checked24786 : (cuts24786.take 2).map (fun c => (3252682753-1+2*2^9*c.k,102787724251947+c.lower,102788106206459+c.upper)) = pointBounds24786 := by
 decide +kernel
def cuts24787 : List PrefixCut := [⟨87,350452830,350453024⟩,
⟨128,518061083,518061373⟩]
theorem checked24787 : checkPrefixCuts (2^48) 3252813825 9 Manual.Count131072.C024787.packed 128 cuts24787 = true := by
 decide +kernel
def pointBounds24787 : List (Nat × Nat × Nat) := [(3252902912,102788585950492,102788967905484)]
theorem point_links_checked24787 : (cuts24787.take 1).map (fun c => (3252813825-1+2*2^9*c.k,102788235497662+c.lower,102788617452460+c.upper)) = pointBounds24787 := by
 decide +kernel
def cuts24788 : List PrefixCut := [⟨59,242106594,242106726⟩,
⟨128,527731314,527731600⟩]
theorem checked24788 : checkPrefixCuts (2^48) 3252944897 9 Manual.Count131072.C024788.packed 128 cuts24788 = true := by
 decide +kernel
def pointBounds24788 : List (Nat × Nat × Nat) := [(3253005312,102788995665339,102789377620559)]
theorem point_links_checked24788 : (cuts24788.take 1).map (fun c => (3252944897-1+2*2^9*c.k,102788753558745+c.lower,102789135513833+c.upper)) = pointBounds24788 := by
 decide +kernel
def cuts24789 : List PrefixCut := [⟨31,124769537,124769608⟩,
⟨128,513433574,513433868⟩]
theorem checked24789 : checkPrefixCuts (2^48) 3253075969 9 Manual.Count131072.C024789.packed 128 cuts24789 = true := by
 decide +kernel
def pointBounds24789 : List (Nat × Nat × Nat) := [(3253107712,102789406059596,102789788015041)]
theorem point_links_checked24789 : (cuts24789.take 1).map (fun c => (3253075969-1+2*2^9*c.k,102789281290059+c.lower,102789663245433+c.upper)) = pointBounds24789 := by
 decide +kernel
def cuts24790 : List PrefixCut := [⟨3,12026591,12026597⟩,
⟨103,410974193,410974418⟩,
⟨128,515835383,515835669⟩]
theorem checked24790 : checkPrefixCuts (2^48) 3253207041 9 Manual.Count131072.C024790.packed 128 cuts24790 = true := by
 decide +kernel
def pointBounds24790 : List (Nat × Nat × Nat) := [(3253210112,102789806750224,102790188705898),(3253312512,102790205697826,102790587653719)]
theorem point_links_checked24790 : (cuts24790.take 2).map (fun c => (3253207041-1+2*2^9*c.k,102789794723633+c.lower,102790176679301+c.upper)) = pointBounds24790 := by
 decide +kernel
def cuts24791 : List PrefixCut := [⟨75,304369516,304369685⟩,
⟨128,519188822,519189113⟩]
theorem checked24791 : checkPrefixCuts (2^48) 3253338113 9 Manual.Count131072.C024791.packed 128 cuts24791 = true := by
 decide +kernel
def pointBounds24791 : List (Nat × Nat × Nat) := [(3253414912,102790614928532,102790996884655)]
theorem point_links_checked24791 : (cuts24791.take 1).map (fun c => (3253338113-1+2*2^9*c.k,102790310559016+c.lower,102790692514970+c.upper)) = pointBounds24791 := by
 decide +kernel
def cuts24792 : List PrefixCut := [⟨47,191803024,191803129⟩,
⟨128,517870254,517870540⟩]
theorem checked24792 : checkPrefixCuts (2^48) 3253469185 9 Manual.Count131072.C024792.packed 128 cuts24792 = true := by
 decide +kernel
def pointBounds24792 : List (Nat × Nat × Nat) := [(3253517312,102791021550862,102791403507212)]
theorem point_links_checked24792 : (cuts24792.take 1).map (fun c => (3253469185-1+2*2^9*c.k,102790829747838+c.lower,102791211704083+c.upper)) = pointBounds24792 := by
 decide +kernel
def cuts24793 : List PrefixCut := [⟨19,78379475,78379518⟩,
⟨119,473470346,473470619⟩,
⟨128,510322949,510323244⟩]
theorem checked24793 : checkPrefixCuts (2^48) 3253600257 9 Manual.Count131072.C024793.packed 128 cuts24793 = true := by
 decide +kernel
def pointBounds24793 : List (Nat × Nat × Nat) := [(3253619712,102791425997567,102791807954141),(3253722112,102791821088438,102792203045242)]
theorem point_links_checked24793 : (cuts24793.take 2).map (fun c => (3253600257-1+2*2^9*c.k,102791347618092+c.lower,102791729574623+c.upper)) = pointBounds24793 := by
 decide +kernel
def cuts24794 : List PrefixCut := [⟨91,374056750,374056965⟩,
⟨128,524922100,524922400⟩]
theorem checked24794 : checkPrefixCuts (2^48) 3253731329 9 Manual.Count131072.C024794.packed 128 cuts24794 = true := by
 decide +kernel
def pointBounds24794 : List (Nat × Nat × Nat) := [(3253824512,102792231997791,102792613954832)]
theorem point_links_checked24794 : (cuts24794.take 1).map (fun c => (3253731329-1+2*2^9*c.k,102791857941041+c.lower,102792239897867+c.upper)) = pointBounds24794 := by
 decide +kernel
def cuts24795 : List PrefixCut := [⟨63,252937678,252937820⟩,
⟨128,516856085,516856370⟩]
theorem checked24795 : checkPrefixCuts (2^48) 3253862401 9 Manual.Count131072.C024795.packed 128 cuts24795 = true := by
 decide +kernel
def pointBounds24795 : List (Nat × Nat × Nat) := [(3253926912,102792635800819,102793017758087)]
theorem point_links_checked24795 : (cuts24795.take 1).map (fun c => (3253862401-1+2*2^9*c.k,102792382863141+c.lower,102792764820267+c.upper)) = pointBounds24795 := by
 decide +kernel
def cuts24796 : List PrefixCut := [⟨35,142120973,142121056⟩,
⟨128,517094840,517095133⟩]
theorem checked24796 : checkPrefixCuts (2^48) 3253993473 9 Manual.Count131072.C024796.packed 128 cuts24796 = true := by
 decide +kernel
def pointBounds24796 : List (Nat × Nat × Nat) := [(3254029312,102793041840199,102793423797693)]
theorem point_links_checked24796 : (cuts24796.take 1).map (fun c => (3253993473-1+2*2^9*c.k,102792899719226+c.lower,102793281676637+c.upper)) = pointBounds24796 := by
 decide +kernel
def cuts24797 : List PrefixCut := [⟨7,27333303,27333318⟩,
⟨107,433779566,433779812⟩,
⟨128,519928284,519928573⟩]
theorem checked24797 : checkPrefixCuts (2^48) 3254124545 9 Manual.Count131072.C024797.packed 128 cuts24797 = true := by
 decide +kernel
def pointBounds24797 : List (Nat × Nat × Nat) := [(3254131712,102793444147369,102793826105088),(3254234112,102793850593632,102794232551582)]
theorem point_links_checked24797 : (cuts24797.take 2).map (fun c => (3254124545-1+2*2^9*c.k,102793416814066+c.lower,102793798771770+c.upper)) = pointBounds24797 := by
 decide +kernel
def cuts24798 : List PrefixCut := [⟨79,326685302,326685475⟩,
⟨128,523021193,523021479⟩]
theorem checked24798 : checkPrefixCuts (2^48) 3254255617 9 Manual.Count131072.C024798.packed 128 cuts24798 = true := by
 decide +kernel
def pointBounds24798 : List (Nat × Nat × Nat) := [(3254336512,102794263427652,102794645385818)]
theorem point_links_checked24798 : (cuts24798.take 1).map (fun c => (3254255617-1+2*2^9*c.k,102793936742350+c.lower,102794318700343+c.upper)) = pointBounds24798 := by
 decide +kernel
def cuts24799 : List PrefixCut := [⟨51,207490038,207490153⟩,
⟨128,522913518,522913812⟩]
theorem checked24799 : checkPrefixCuts (2^48) 3254386689 9 Manual.Count131072.C024799.packed 128 cuts24799 = true := by
 decide +kernel
def pointBounds24799 : List (Nat × Nat × Nat) := [(3254438912,102794667253581,102795049211975)]
theorem point_links_checked24799 : (cuts24799.take 1).map (fun c => (3254386689-1+2*2^9*c.k,102794459763543+c.lower,102794841721822+c.upper)) = pointBounds24799 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000149
