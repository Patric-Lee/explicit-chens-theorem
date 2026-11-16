import PlattAssemblyKernel
import PlattCertificates.Count131072.C019760
import PlattCertificates.Count131072.C019761
import PlattCertificates.Count131072.C019762
import PlattCertificates.Count131072.C019763
import PlattCertificates.Count131072.C019764
import PlattCertificates.Count131072.C019765
import PlattCertificates.Count131072.C019766
import PlattCertificates.Count131072.C019767
import PlattCertificates.Count131072.C019768
import PlattCertificates.Count131072.C019769
import PlattCertificates.Count131072.C019770
import PlattCertificates.Count131072.C019771
import PlattCertificates.Count131072.C019772
import PlattCertificates.Count131072.C019773
import PlattCertificates.Count131072.C019774
import PlattCertificates.Count131072.C019775
import PlattCertificates.Count131072.C019776
import PlattCertificates.Count131072.C019777
import PlattCertificates.Count131072.C019778
import PlattCertificates.Count131072.C019779
import PlattCertificates.Count131072.C019780
import PlattCertificates.Count131072.C019781
import PlattCertificates.Count131072.C019782
import PlattCertificates.Count131072.C019783
import PlattCertificates.Count131072.C019784
import PlattCertificates.Count131072.C019785
import PlattCertificates.Count131072.C019786
import PlattCertificates.Count131072.C019787
import PlattCertificates.Count131072.C019788
import PlattCertificates.Count131072.C019789
import PlattCertificates.Count131072.C019790
import PlattCertificates.Count131072.C019791
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000305
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts19760 : List PrefixCut := [⟨45,231348838,231348973⟩,
⟨125,642492891,642493266⟩,
⟨128,657358504,657358888⟩]
theorem checked19760 : checkPrefixCuts (2^48) 2593914881 9 Manual.Count131072.C019760.packed 128 cuts19760 = true := by
 decide +kernel
def pointBounds19760 : List (Nat × Nat × Nat) := [(2593960960,99864649219575,99865029497368),(2594042880,99865060363628,99865440641661)]
theorem point_links_checked19760 : (cuts19760.take 2).map (fun c => (2593914881-1+2*2^9*c.k,99864417870737+c.lower,99864798148395+c.upper)) = pointBounds19760 := by
 decide +kernel
def cuts19761 : List PrefixCut := [⟨77,394203794,394204024⟩,
⟨128,654504052,654504435⟩]
theorem checked19761 : checkPrefixCuts (2^48) 2594045953 9 Manual.Count131072.C019761.packed 128 cuts19761 = true := by
 decide +kernel
def pointBounds19761 : List (Nat × Nat × Nat) := [(2594124800,99865469433035,99865849711307)]
theorem point_links_checked19761 : (cuts19761.take 1).map (fun c => (2594045953-1+2*2^9*c.k,99865075229241+c.lower,99865455507283+c.upper)) = pointBounds19761 := by
 decide +kernel
def cuts19762 : List PrefixCut := [⟨29,147345663,147345747⟩,
⟨109,554870334,554870656⟩,
⟨128,650348143,650348520⟩]
theorem checked19762 : checkPrefixCuts (2^48) 2594177025 9 Manual.Count131072.C019762.packed 128 cuts19762 = true := by
 decide +kernel
def pointBounds19762 : List (Nat × Nat × Nat) := [(2594206720,99865877078956,99866257357465),(2594288640,99866284603627,99866664882374)]
theorem point_links_checked19762 : (cuts19762.take 2).map (fun c => (2594177025-1+2*2^9*c.k,99865729733293+c.lower,99866110011718+c.upper)) = pointBounds19762 := by
 decide +kernel
def cuts19763 : List PrefixCut := [⟨61,318435119,318435303⟩,
⟨128,664744929,664745318⟩]
theorem checked19763 : checkPrefixCuts (2^48) 2594308097 9 Manual.Count131072.C019763.packed 128 cuts19763 = true := by
 decide +kernel
def pointBounds19763 : List (Nat × Nat × Nat) := [(2594370560,99866698516555,99867078795541)]
theorem point_links_checked19763 : (cuts19763.take 1).map (fun c => (2594308097-1+2*2^9*c.k,99866380081436+c.lower,99866760360238+c.upper)) = pointBounds19763 := by
 decide +kernel
def cuts19764 : List PrefixCut := [⟨13,65528768,65528805⟩,
⟨93,471712900,471713178⟩,
⟨128,652669041,652669424⟩]
theorem checked19764 : checkPrefixCuts (2^48) 2594439169 9 Manual.Count131072.C019764.packed 128 cuts19764 = true := by
 decide +kernel
def pointBounds19764 : List (Nat × Nat × Nat) := [(2594452480,99867110355133,99867490634361),(2594534400,99867516539265,99867896818734)]
theorem point_links_checked19764 : (cuts19764.take 2).map (fun c => (2594439169-1+2*2^9*c.k,99867044826365+c.lower,99867425105556+c.upper)) = pointBounds19764 := by
 decide +kernel
def cuts19765 : List PrefixCut := [⟨45,233677028,233677163⟩,
⟨125,643089990,643090369⟩,
⟨128,657843367,657843755⟩]
theorem checked19765 : checkPrefixCuts (2^48) 2594570241 9 Manual.Count131072.C019765.packed 128 cuts19765 = true := by
 decide +kernel
def pointBounds19765 : List (Nat × Nat × Nat) := [(2594616320,99867931172434,99868311452143),(2594698240,99868340585396,99868720865349)]
theorem point_links_checked19765 : (cuts19765.take 2).map (fun c => (2594570241-1+2*2^9*c.k,99867697495406+c.lower,99868077774980+c.upper)) = pointBounds19765 := by
 decide +kernel
def cuts19766 : List PrefixCut := [⟨77,401914711,401914950⟩,
⟨128,666705253,666705642⟩]
theorem checked19766 : checkPrefixCuts (2^48) 2594701313 9 Manual.Count131072.C019766.packed 128 cuts19766 = true := by
 decide +kernel
def pointBounds19766 : List (Nat × Nat × Nat) := [(2594780160,99868757253484,99869137533685)]
theorem point_links_checked19766 : (cuts19766.take 1).map (fun c => (2594701313-1+2*2^9*c.k,99868355338773+c.lower,99868735618735+c.upper)) = pointBounds19766 := by
 decide +kernel
def cuts19767 : List PrefixCut := [⟨29,145789802,145789888⟩,
⟨109,551909773,551910096⟩,
⟨128,646821117,646821497⟩]
theorem checked19767 : checkPrefixCuts (2^48) 2594832385 9 Manual.Count131072.C019767.packed 128 cuts19767 = true := by
 decide +kernel
def pointBounds19767 : List (Nat × Nat × Nat) := [(2594862080,99869167833828,99869548114265),(2594944000,99869573953799,99869954234473)]
theorem point_links_checked19767 : (cuts19767.take 2).map (fun c => (2594832385-1+2*2^9*c.k,99869022044026+c.lower,99869402324377+c.upper)) = pointBounds19767 := by
 decide +kernel
def cuts19768 : List PrefixCut := [⟨61,314341388,314341569⟩,
⟨128,658069045,658069428⟩]
theorem checked19768 : checkPrefixCuts (2^48) 2594963457 9 Manual.Count131072.C019768.packed 128 cuts19768 = true := by
 decide +kernel
def pointBounds19768 : List (Nat × Nat × Nat) := [(2595025920,99869983206531,99870363487443)]
theorem point_links_checked19768 : (cuts19768.take 1).map (fun c => (2594963457-1+2*2^9*c.k,99869668865143+c.lower,99870049145874+c.upper)) = pointBounds19768 := by
 decide +kernel
def cuts19769 : List PrefixCut := [⟨13,67464570,67464608⟩,
⟨93,481030001,481030281⟩,
⟨128,661072761,661073149⟩]
theorem checked19769 : checkPrefixCuts (2^48) 2595094529 9 Manual.Count131072.C019769.packed 128 cuts19769 = true := by
 decide +kernel
def pointBounds19769 : List (Nat × Nat × Nat) := [(2595107840,99870394398758,99870774679910),(2595189760,99870807964189,99871188245583)]
theorem point_links_checked19769 : (cuts19769.take 2).map (fun c => (2595094529-1+2*2^9*c.k,99870326934188+c.lower,99870707215302+c.upper)) = pointBounds19769 := by
 decide +kernel
def cuts19770 : List PrefixCut := [⟨45,229171303,229171440⟩,
⟨125,634793444,634793818⟩,
⟨128,649760002,649760385⟩]
theorem checked19770 : checkPrefixCuts (2^48) 2595225601 9 Manual.Count131072.C019770.packed 128 cuts19770 = true := by
 decide +kernel
def pointBounds19770 : List (Nat × Nat × Nat) := [(2595271680,99871217178252,99871597459891),(2595353600,99871622800393,99872003082269)]
theorem point_links_checked19770 : (cuts19770.take 2).map (fun c => (2595225601-1+2*2^9*c.k,99870988006949+c.lower,99871368288451+c.upper)) = pointBounds19770 := by
 decide +kernel
def cuts19771 : List PrefixCut := [⟨77,396715958,396716197⟩,
⟨128,661114303,661114696⟩]
theorem checked19771 : checkPrefixCuts (2^48) 2595356673 9 Manual.Count131072.C019771.packed 128 cuts19771 = true := by
 decide +kernel
def pointBounds19771 : List (Nat × Nat × Nat) := [(2595435520,99872034482909,99872414765033)]
theorem point_links_checked19771 : (cuts19771.take 1).map (fun c => (2595356673-1+2*2^9*c.k,99871637766951+c.lower,99872018048836+c.upper)) = pointBounds19771 := by
 decide +kernel
def cuts19772 : List PrefixCut := [⟨29,144343181,144343267⟩,
⟨109,556433599,556433930⟩,
⟨128,652947622,652948010⟩]
theorem checked19772 : checkPrefixCuts (2^48) 2595487745 9 Manual.Count131072.C019772.packed 128 cuts19772 = true := by
 decide +kernel
def pointBounds19772 : List (Nat × Nat × Nat) := [(2595517440,99872443224435,99872823506799),(2595599360,99872855314853,99873235597462)]
theorem point_links_checked19772 : (cuts19772.take 2).map (fun c => (2595487745-1+2*2^9*c.k,99872298881254+c.lower,99872679163532+c.upper)) = pointBounds19772 := by
 decide +kernel
def cuts19773 : List PrefixCut := [⟨61,314478915,314479102⟩,
⟨128,657794391,657794783⟩]
theorem checked19773 : checkPrefixCuts (2^48) 2595618817 9 Manual.Count131072.C019773.packed 128 cuts19773 = true := by
 decide +kernel
def pointBounds19773 : List (Nat × Nat × Nat) := [(2595681280,99873266307791,99873646590644)]
theorem point_links_checked19773 : (cuts19773.take 1).map (fun c => (2595618817-1+2*2^9*c.k,99872951828876+c.lower,99873332111542+c.upper)) = pointBounds19773 := by
 decide +kernel
def cuts19774 : List PrefixCut := [⟨13,66363168,66363207⟩,
⟨93,479607288,479607571⟩,
⟨128,656460037,656460426⟩]
theorem checked19774 : checkPrefixCuts (2^48) 2595749889 9 Manual.Count131072.C019774.packed 128 cuts19774 = true := by
 decide +kernel
def pointBounds19774 : List (Nat × Nat × Nat) := [(2595763200,99873675986435,99874056269532),(2595845120,99874089230555,99874469513896)]
theorem point_links_checked19774 : (cuts19774.take 2).map (fun c => (2595749889-1+2*2^9*c.k,99873609623267+c.lower,99873989906325+c.upper)) = pointBounds19774 := by
 decide +kernel
def cuts19775 : List PrefixCut := [⟨45,231065179,231065316⟩,
⟨125,639295541,639295919⟩,
⟨128,655451006,655451393⟩]
theorem checked19775 : checkPrefixCuts (2^48) 2595880961 9 Manual.Count131072.C019775.packed 128 cuts19775 = true := by
 decide +kernel
def pointBounds19775 : List (Nat × Nat × Nat) := [(2595927040,99874497148483,99874877432067),(2596008960,99874905378845,99875285662670)]
theorem point_links_checked19775 : (cuts19775.take 2).map (fun c => (2595880961-1+2*2^9*c.k,99874266083304+c.lower,99874646366751+c.upper)) = pointBounds19775 := by
 decide +kernel
def cuts19776 : List PrefixCut := [⟨77,395856942,395857175⟩,
⟨128,659538008,659538390⟩]
theorem checked19776 : checkPrefixCuts (2^48) 2596012033 9 Manual.Count131072.C019776.packed 128 cuts19776 = true := by
 decide +kernel
def pointBounds19776 : List (Nat × Nat × Nat) := [(2596090880,99875317391252,99875697675319)]
theorem point_links_checked19776 : (cuts19776.take 1).map (fun c => (2596012033-1+2*2^9*c.k,99874921534310+c.lower,99875301818144+c.upper)) = pointBounds19776 := by
 decide +kernel
def cuts19777 : List PrefixCut := [⟨29,144523599,144523682⟩,
⟨109,553799559,553799886⟩,
⟨128,652132270,652132655⟩]
theorem checked19777 : checkPrefixCuts (2^48) 2596143105 9 Manual.Count131072.C019777.packed 128 cuts19777 = true := by
 decide +kernel
def pointBounds19777 : List (Nat × Nat × Nat) := [(2596172800,99875725595917,99876105880216),(2596254720,99876134871877,99876515156420)]
theorem point_links_checked19777 : (cuts19777.take 2).map (fun c => (2596143105-1+2*2^9*c.k,99875581072318+c.lower,99875961356534+c.upper)) = pointBounds19777 := by
 decide +kernel
def cuts19778 : List PrefixCut := [⟨61,314182677,314182864⟩,
⟨128,656869507,656869891⟩]
theorem checked19778 : checkPrefixCuts (2^48) 2596274177 9 Manual.Count131072.C019778.packed 128 cuts19778 = true := by
 decide +kernel
def pointBounds19778 : List (Nat × Nat × Nat) := [(2596336640,99876547387265,99876927672053)]
theorem point_links_checked19778 : (cuts19778.take 1).map (fun c => (2596274177-1+2*2^9*c.k,99876233204588+c.lower,99876613489189+c.upper)) = pointBounds19778 := by
 decide +kernel
def cuts19779 : List PrefixCut := [⟨13,65912783,65912823⟩,
⟨93,471030414,471030698⟩,
⟨128,647946945,647947336⟩]
theorem checked19779 : checkPrefixCuts (2^48) 2596405249 9 Manual.Count131072.C019779.packed 128 cuts19779 = true := by
 decide +kernel
def pointBounds19779 : List (Nat × Nat × Nat) := [(2596418560,99876955986878,99877336271903),(2596500480,99877361104509,99877741389778)]
theorem point_links_checked19779 : (cuts19779.take 2).map (fun c => (2596405249-1+2*2^9*c.k,99876890074095+c.lower,99877270359080+c.upper)) = pointBounds19779 := by
 decide +kernel
def cuts19780 : List PrefixCut := [⟨45,231765690,231765825⟩,
⟨125,640218251,640218625⟩,
⟨128,656694836,656695219⟩]
theorem checked19780 : checkPrefixCuts (2^48) 2596536321 9 Manual.Count131072.C019780.packed 128 cuts19780 = true := by
 decide +kernel
def pointBounds19780 : List (Nat × Nat × Nat) := [(2596582400,99877769786730,99878150072241),(2596664320,99878178239291,99878558525041)]
theorem point_links_checked19780 : (cuts19780.take 2).map (fun c => (2596536321-1+2*2^9*c.k,99877538021040+c.lower,99877918306416+c.upper)) = pointBounds19780 := by
 decide +kernel
def cuts19781 : List PrefixCut := [⟨77,390662395,390662627⟩,
⟨128,655794444,655794830⟩]
theorem checked19781 : checkPrefixCuts (2^48) 2596667393 9 Manual.Count131072.C019781.packed 128 cuts19781 = true := by
 decide +kernel
def pointBounds19781 : List (Nat × Nat × Nat) := [(2596746240,99878585378271,99878965664262)]
theorem point_links_checked19781 : (cuts19781.take 1).map (fun c => (2596667393-1+2*2^9*c.k,99878194715876+c.lower,99878575001635+c.upper)) = pointBounds19781 := by
 decide +kernel
def cuts19782 : List PrefixCut := [⟨29,150882256,150882347⟩,
⟨109,553768263,553768587⟩,
⟨128,654243926,654244308⟩]
theorem checked19782 : checkPrefixCuts (2^48) 2596798465 9 Manual.Count131072.C019782.packed 128 cuts19782 = true := by
 decide +kernel
def pointBounds19782 : List (Nat × Nat × Nat) := [(2596828160,99879001392576,99879381678812),(2596910080,99879404278583,99879784565052)]
theorem point_links_checked19782 : (cuts19782.take 2).map (fun c => (2596798465-1+2*2^9*c.k,99878850510320+c.lower,99879230796465+c.upper)) = pointBounds19782 := by
 decide +kernel
def cuts19783 : List PrefixCut := [⟨61,316813047,316813230⟩,
⟨128,660822378,660822764⟩]
theorem checked19783 : checkPrefixCuts (2^48) 2596929537 9 Manual.Count131072.C019783.packed 128 cuts19783 = true := by
 decide +kernel
def pointBounds19783 : List (Nat × Nat × Nat) := [(2596992000,99879821567293,99880201854003)]
theorem point_links_checked19783 : (cuts19783.take 1).map (fun c => (2596929537-1+2*2^9*c.k,99879504754246+c.lower,99879885040773+c.upper)) = pointBounds19783 := by
 decide +kernel
def cuts19784 : List PrefixCut := [⟨13,66329681,66329721⟩,
⟨93,476222289,476222569⟩,
⟨128,654286332,654286721⟩]
theorem checked19784 : checkPrefixCuts (2^48) 2597060609 9 Manual.Count131072.C019784.packed 128 cuts19784 = true := by
 decide +kernel
def pointBounds19784 : List (Nat × Nat × Nat) := [(2597073920,99880231906305,99880612193258),(2597155840,99880641798913,99881022086106)]
theorem point_links_checked19784 : (cuts19784.take 2).map (fun c => (2597060609-1+2*2^9*c.k,99880165576624+c.lower,99880545863537+c.upper)) = pointBounds19784 := by
 decide +kernel
def cuts19785 : List PrefixCut := [⟨45,235933827,235933965⟩,
⟨125,638322792,638323169⟩,
⟨128,652411051,652411437⟩]
theorem checked19785 : checkPrefixCuts (2^48) 2597191681 9 Manual.Count131072.C019785.packed 128 cuts19785 = true := by
 decide +kernel
def pointBounds19785 : List (Nat × Nat × Nat) := [(2597237760,99881055796783,99881436084223),(2597319680,99881458185748,99881838473427)]
theorem point_links_checked19785 : (cuts19785.take 2).map (fun c => (2597191681-1+2*2^9*c.k,99880819862956+c.lower,99881200150258+c.upper)) = pointBounds19785 := by
 decide +kernel
def cuts19786 : List PrefixCut := [⟨77,390238668,390238895⟩,
⟨128,649452034,649452413⟩]
theorem checked19786 : checkPrefixCuts (2^48) 2597322753 9 Manual.Count131072.C019786.packed 128 cuts19786 = true := by
 decide +kernel
def pointBounds19786 : List (Nat × Nat × Nat) := [(2597401600,99881862512675,99882242800590)]
theorem point_links_checked19786 : (cuts19786.take 1).map (fun c => (2597322753-1+2*2^9*c.k,99881472274007+c.lower,99881852561695+c.upper)) = pointBounds19786 := by
 decide +kernel
def cuts19787 : List PrefixCut := [⟨29,143800455,143800535⟩,
⟨109,553736774,553737094⟩,
⟨128,652670031,652670410⟩]
theorem checked19787 : checkPrefixCuts (2^48) 2597453825 9 Manual.Count131072.C019787.packed 128 cuts19787 = true := by
 decide +kernel
def pointBounds19787 : List (Nat × Nat × Nat) := [(2597483520,99882265526496,99882645814643),(2597565440,99882675462815,99883055751202)]
theorem point_links_checked19787 : (cuts19787.take 2).map (fun c => (2597453825-1+2*2^9*c.k,99882121726041+c.lower,99882502014108+c.upper)) = pointBounds19787 := by
 decide +kernel
def cuts19788 : List PrefixCut := [⟨61,315649552,315649739⟩,
⟨128,668890789,668891179⟩]
theorem checked19788 : checkPrefixCuts (2^48) 2597584897 9 Manual.Count131072.C019788.packed 128 cuts19788 = true := by
 decide +kernel
def pointBounds19788 : List (Nat × Nat × Nat) := [(2597647360,99883090045624,99883470334257)]
theorem point_links_checked19788 : (cuts19788.take 1).map (fun c => (2597584897-1+2*2^9*c.k,99882774396072+c.lower,99883154684518+c.upper)) = pointBounds19788 := by
 decide +kernel
def cuts19789 : List PrefixCut := [⟨13,68046619,68046657⟩,
⟨93,475668782,475669064⟩,
⟨128,654879751,654880142⟩]
theorem checked19789 : checkPrefixCuts (2^48) 2597715969 9 Manual.Count131072.C019789.packed 128 cuts19789 = true := by
 decide +kernel
def pointBounds19789 : List (Nat × Nat × Nat) := [(2597729280,99883511333480,99883891622354),(2597811200,99883918955643,99884299244761)]
theorem point_links_checked19789 : (cuts19789.take 2).map (fun c => (2597715969-1+2*2^9*c.k,99883443286861+c.lower,99883823575697+c.upper)) = pointBounds19789 := by
 decide +kernel
def cuts19790 : List PrefixCut := [⟨45,225689580,225689713⟩,
⟨125,633827725,633828104⟩,
⟨128,649862620,649863010⟩]
theorem checked19790 : checkPrefixCuts (2^48) 2597847041 9 Manual.Count131072.C019790.packed 128 cuts19790 = true := by
 decide +kernel
def pointBounds19790 : List (Nat × Nat × Nat) := [(2597893120,99884323856192,99884704145552),(2597975040,99884731994337,99885112283943)]
theorem point_links_checked19790 : (cuts19790.take 2).map (fun c => (2597847041-1+2*2^9*c.k,99884098166612+c.lower,99884478455839+c.upper)) = pointBounds19790 := by
 decide +kernel
def cuts19791 : List PrefixCut := [⟨77,396749131,396749362⟩,
⟨128,654922022,654922409⟩]
theorem checked19791 : checkPrefixCuts (2^48) 2597978113 9 Manual.Count131072.C019791.packed 128 cuts19791 = true := by
 decide +kernel
def pointBounds19791 : List (Nat × Nat × Nat) := [(2598056960,99885144778363,99885525068211)]
theorem point_links_checked19791 : (cuts19791.take 1).map (fun c => (2597978113-1+2*2^9*c.k,99884748029232+c.lower,99885128318849+c.upper)) = pointBounds19791 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000305
