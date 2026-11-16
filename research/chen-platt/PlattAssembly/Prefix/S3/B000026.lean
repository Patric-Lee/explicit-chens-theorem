import PlattAssemblyKernel
import PlattCertificates.Count131072.C020832
import PlattCertificates.Count131072.C020833
import PlattCertificates.Count131072.C020834
import PlattCertificates.Count131072.C020835
import PlattCertificates.Count131072.C020836
import PlattCertificates.Count131072.C020837
import PlattCertificates.Count131072.C020838
import PlattCertificates.Count131072.C020839
import PlattCertificates.Count131072.C020840
import PlattCertificates.Count131072.C020841
import PlattCertificates.Count131072.C020842
import PlattCertificates.Count131072.C020843
import PlattCertificates.Count131072.C020844
import PlattCertificates.Count131072.C020845
import PlattCertificates.Count131072.C020846
import PlattCertificates.Count131072.C020847
import PlattCertificates.Count131072.C020848
import PlattCertificates.Count131072.C020849
import PlattCertificates.Count131072.C020850
import PlattCertificates.Count131072.C020851
import PlattCertificates.Count131072.C020852
import PlattCertificates.Count131072.C020853
import PlattCertificates.Count131072.C020854
import PlattCertificates.Count131072.C020855
import PlattCertificates.Count131072.C020856
import PlattCertificates.Count131072.C020857
import PlattCertificates.Count131072.C020858
import PlattCertificates.Count131072.C020859
import PlattCertificates.Count131072.C020860
import PlattCertificates.Count131072.C020861
import PlattCertificates.Count131072.C020862
import PlattCertificates.Count131072.C020863
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000026
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts20832 : List PrefixCut := [⟨1,4529251,4529254⟩,
⟨85,408964327,408964562⟩,
⟨128,617610388,617610744⟩]
theorem checked20832 : checkPrefixCuts (2^48) 2734424065 9 Manual.Count131072.C020832.packed 128 cuts20832 = true := by
 decide +kernel
def pointBounds20832 : List (Nat × Nat × Nat) := [(2734425088,100548486468550,100548867146538),(2734511104,100548890903626,100549271581846)]
theorem point_links_checked20832 : (cuts20832.take 2).map (fun c => (2734424065-1+2*2^9*c.k,100548481939299+c.lower,100548862617284+c.upper)) = pointBounds20832 := by
 decide +kernel
def cuts20833 : List PrefixCut := [⟨41,196599763,196599877⟩,
⟨125,608420307,608420662⟩,
⟨128,623241901,623242265⟩]
theorem checked20833 : checkPrefixCuts (2^48) 2734555137 9 Manual.Count131072.C020833.packed 128 cuts20833 = true := by
 decide +kernel
def pointBounds20833 : List (Nat × Nat × Nat) := [(2734597120,100549296149450,100549676827905),(2734683136,100549707969994,100550088648690)]
theorem point_links_checked20833 : (cuts20833.take 2).map (fun c => (2734555137-1+2*2^9*c.k,100549099549687+c.lower,100549480228028+c.upper)) = pointBounds20833 := by
 decide +kernel
def cuts20834 : List PrefixCut := [⟨81,392251440,392251669⟩,
⟨128,616419156,616419513⟩]
theorem checked20834 : checkPrefixCuts (2^48) 2734686209 9 Manual.Count131072.C020834.packed 128 cuts20834 = true := by
 decide +kernel
def pointBounds20834 : List (Nat × Nat × Nat) := [(2734769152,100550115043028,100550495721962)]
theorem point_links_checked20834 : (cuts20834.take 1).map (fun c => (2734686209-1+2*2^9*c.k,100549722791588+c.lower,100550103470293+c.upper)) = pointBounds20834 := by
 decide +kernel
def cuts20835 : List PrefixCut := [⟨37,184230444,184230551⟩,
⟨121,591895328,591895671⟩,
⟨128,626372838,626373200⟩]
theorem checked20835 : checkPrefixCuts (2^48) 2734817281 9 Manual.Count131072.C020835.packed 128 cuts20835 = true := by
 decide +kernel
def pointBounds20835 : List (Nat × Nat × Nat) := [(2734855168,100550523441188,100550904120357),(2734941184,100550931106072,100551311785477)]
theorem point_links_checked20835 : (cuts20835.take 2).map (fun c => (2734817281-1+2*2^9*c.k,100550339210744+c.lower,100550719889806+c.upper)) = pointBounds20835 := by
 decide +kernel
def cuts20836 : List PrefixCut := [⟨77,370087092,370087311⟩,
⟨128,615433747,615434110⟩]
theorem checked20836 : checkPrefixCuts (2^48) 2734948353 9 Manual.Count131072.C020836.packed 128 cuts20836 = true := by
 decide +kernel
def pointBounds20836 : List (Nat × Nat × Nat) := [(2735027200,100551335670674,100551716350317)]
theorem point_links_checked20836 : (cuts20836.take 1).map (fun c => (2734948353-1+2*2^9*c.k,100550965583582+c.lower,100551346263006+c.upper)) = pointBounds20836 := by
 decide +kernel
def cuts20837 : List PrefixCut := [⟨33,157044066,157044157⟩,
⟨117,560965832,560966157⟩,
⟨128,615918790,615919148⟩]
theorem checked20837 : checkPrefixCuts (2^48) 2735079425 9 Manual.Count131072.C020837.packed 128 cuts20837 = true := by
 decide +kernel
def pointBounds20837 : List (Nat × Nat × Nat) := [(2735113216,100551738061395,100552118741273),(2735199232,100552141983161,100552522663273)]
theorem point_links_checked20837 : (cuts20837.take 2).map (fun c => (2735079425-1+2*2^9*c.k,100551581017329+c.lower,100551961697116+c.upper)) = pointBounds20837 := by
 decide +kernel
def cuts20838 : List PrefixCut := [⟨73,348441486,348441689⟩,
⟨128,613316573,613316924⟩]
theorem checked20838 : checkPrefixCuts (2^48) 2735210497 9 Manual.Count131072.C020838.packed 128 cuts20838 = true := by
 decide +kernel
def pointBounds20838 : List (Nat × Nat × Nat) := [(2735285248,100552545377605,100552926057953)]
theorem point_links_checked20838 : (cuts20838.take 1).map (fun c => (2735210497-1+2*2^9*c.k,100552196936119+c.lower,100552577616264+c.upper)) = pointBounds20838 := by
 decide +kernel
def cuts20839 : List PrefixCut := [⟨29,141593773,141593853⟩,
⟨113,545374512,545374824⟩,
⟨128,614213523,614213879⟩]
theorem checked20839 : checkPrefixCuts (2^48) 2735341569 9 Manual.Count131072.C020839.packed 128 cuts20839 = true := by
 decide +kernel
def pointBounds20839 : List (Nat × Nat × Nat) := [(2735371264,100552951846465,100553332527041),(2735457280,100553355627204,100553736308012)]
theorem point_links_checked20839 : (cuts20839.take 2).map (fun c => (2735341569-1+2*2^9*c.k,100552810252692+c.lower,100553190933188+c.upper)) = pointBounds20839 := by
 decide +kernel
def cuts20840 : List PrefixCut := [⟨69,335134767,335134959⟩,
⟨128,620769365,620769726⟩]
theorem checked20840 : checkPrefixCuts (2^48) 2735472641 9 Manual.Count131072.C020840.packed 128 cuts20840 = true := by
 decide +kernel
def pointBounds20840 : List (Nat × Nat × Nat) := [(2735543296,100553759600982,100554140282026)]
theorem point_links_checked20840 : (cuts20840.take 1).map (fun c => (2735472641-1+2*2^9*c.k,100553424466215+c.lower,100553805147067+c.upper)) = pointBounds20840 := by
 decide +kernel
def cuts20841 : List PrefixCut := [⟨25,123368314,123368387⟩,
⟨109,531741000,531741309⟩,
⟨128,627838939,627839303⟩]
theorem checked20841 : checkPrefixCuts (2^48) 2735603713 9 Manual.Count131072.C020841.packed 128 cuts20841 = true := by
 decide +kernel
def pointBounds20841 : List (Nat × Nat × Nat) := [(2735629312,100554168603894,100554549285180),(2735715328,100554576976580,100554957658102)]
theorem point_links_checked20841 : (cuts20841.take 2).map (fun c => (2735603713-1+2*2^9*c.k,100554045235580+c.lower,100554425916793+c.upper)) = pointBounds20841 := by
 decide +kernel
def cuts20842 : List PrefixCut := [⟨65,316068768,316068952⟩,
⟨128,624207915,624208277⟩]
theorem checked20842 : checkPrefixCuts (2^48) 2735734785 9 Manual.Count131072.C020842.packed 128 cuts20842 = true := by
 decide +kernel
def pointBounds20842 : List (Nat × Nat × Nat) := [(2735801344,100554989143287,100555369825048)]
theorem point_links_checked20842 : (cuts20842.take 1).map (fun c => (2735734785-1+2*2^9*c.k,100554673074519+c.lower,100555053756096+c.upper)) = pointBounds20842 := by
 decide +kernel
def cuts20843 : List PrefixCut := [⟨21,102162708,102162769⟩,
⟨105,511628635,511628938⟩,
⟨128,620577298,620577666⟩]
theorem checked20843 : checkPrefixCuts (2^48) 2735865857 9 Manual.Count131072.C020843.packed 128 cuts20843 = true := by
 decide +kernel
def pointBounds20843 : List (Nat × Nat × Nat) := [(2735887360,100555399445142,100555780127142),(2735973376,100555808911069,100556189593311)]
theorem point_links_checked20843 : (cuts20843.take 2).map (fun c => (2735865857-1+2*2^9*c.k,100555297282434+c.lower,100555677964373+c.upper)) = pointBounds20843 := by
 decide +kernel
def cuts20844 : List PrefixCut := [⟨61,289702177,289702340⟩,
⟨128,617975462,617975816⟩]
theorem checked20844 : checkPrefixCuts (2^48) 2735996929 9 Manual.Count131072.C020844.packed 128 cuts20844 = true := by
 decide +kernel
def pointBounds20844 : List (Nat × Nat × Nat) := [(2736059392,100556207561909,100556588244379)]
theorem point_links_checked20844 : (cuts20844.take 1).map (fun c => (2735996929-1+2*2^9*c.k,100555917859732+c.lower,100556298542039+c.upper)) = pointBounds20844 := by
 decide +kernel
def cuts20845 : List PrefixCut := [⟨17,84870320,84870366⟩,
⟨101,488948274,488948561⟩,
⟨128,621649315,621649678⟩]
theorem checked20845 : checkPrefixCuts (2^48) 2736128001 9 Manual.Count131072.C020845.packed 128 cuts20845 = true := by
 decide +kernel
def pointBounds20845 : List (Nat × Nat × Nat) := [(2736145408,100556620705514,100557001388221),(2736231424,100557024783468,100557405466416)]
theorem point_links_checked20845 : (cuts20845.take 2).map (fun c => (2736128001-1+2*2^9*c.k,100556535835194+c.lower,100556916517855+c.upper)) = pointBounds20845 := by
 decide +kernel
def cuts20846 : List PrefixCut := [⟨57,274655953,274656117⟩,
⟨128,608658462,608658821⟩]
theorem checked20846 : checkPrefixCuts (2^48) 2736259073 9 Manual.Count131072.C020846.packed 128 cuts20846 = true := by
 decide +kernel
def pointBounds20846 : List (Nat × Nat × Nat) := [(2736317440,100557432140462,100557812823650)]
theorem point_links_checked20846 : (cuts20846.take 1).map (fun c => (2736259073-1+2*2^9*c.k,100557157484509+c.lower,100557538167533+c.upper)) = pointBounds20846 := by
 decide +kernel
def cuts20847 : List PrefixCut := [⟨13,64701037,64701075⟩,
⟨97,470283818,470284094⟩,
⟨128,621795486,621795853⟩]
theorem checked20847 : checkPrefixCuts (2^48) 2736390145 9 Manual.Count131072.C020847.packed 128 cuts20847 = true := by
 decide +kernel
def pointBounds20847 : List (Nat × Nat × Nat) := [(2736403456,100557830844008,100558211527429),(2736489472,100558236426789,100558617110448)]
theorem point_links_checked20847 : (cuts20847.take 2).map (fun c => (2736390145-1+2*2^9*c.k,100557766142971+c.lower,100558146826354+c.upper)) = pointBounds20847 := by
 decide +kernel
def cuts20848 : List PrefixCut := [⟨53,258378370,258378516⟩,
⟨128,621354304,621354657⟩]
theorem checked20848 : checkPrefixCuts (2^48) 2736521217 9 Manual.Count131072.C020848.packed 128 cuts20848 = true := by
 decide +kernel
def pointBounds20848 : List (Nat × Nat × Nat) := [(2736575488,100558646316827,100559027000723)]
theorem point_links_checked20848 : (cuts20848.take 1).map (fun c => (2736521217-1+2*2^9*c.k,100558387938457+c.lower,100558768622207+c.upper)) = pointBounds20848 := by
 decide +kernel
def cuts20849 : List PrefixCut := [⟨9,43198492,43198518⟩,
⟨93,449257231,449257491⟩,
⟨128,620398767,620399128⟩]
theorem checked20849 : checkPrefixCuts (2^48) 2736652289 9 Manual.Count131072.C020849.packed 128 cuts20849 = true := by
 decide +kernel
def pointBounds20849 : List (Nat × Nat × Nat) := [(2736661504,100559052491253,100559433175382),(2736747520,100559458549992,100559839234355)]
theorem point_links_checked20849 : (cuts20849.take 2).map (fun c => (2736652289-1+2*2^9*c.k,100559009292761+c.lower,100559389976864+c.upper)) = pointBounds20849 := by
 decide +kernel
def cuts20850 : List PrefixCut := [⟨49,240252592,240252738⟩,
⟨128,620677729,620678095⟩]
theorem checked20850 : checkPrefixCuts (2^48) 2736783361 9 Manual.Count131072.C020850.packed 128 cuts20850 = true := by
 decide +kernel
def pointBounds20850 : List (Nat × Nat × Nat) := [(2736833536,100559869944120,100560250628730)]
theorem point_links_checked20850 : (cuts20850.take 1).map (fun c => (2736783361-1+2*2^9*c.k,100559629691528+c.lower,100560010375992+c.upper)) = pointBounds20850 := by
 decide +kernel
def cuts20851 : List PrefixCut := [⟨5,24888195,24888209⟩,
⟨89,431320072,431320327⟩,
⟨128,626098481,626098847⟩]
theorem checked20851 : checkPrefixCuts (2^48) 2736914433 9 Manual.Count131072.C020851.packed 128 cuts20851 = true := by
 decide +kernel
def pointBounds20851 : List (Nat × Nat × Nat) := [(2736919552,100560275257452,100560655942296),(2737005568,100560681689329,100561062374414)]
theorem point_links_checked20851 : (cuts20851.take 2).map (fun c => (2736914433-1+2*2^9*c.k,100560250369257+c.lower,100560631054087+c.upper)) = pointBounds20851 := by
 decide +kernel
def cuts20852 : List PrefixCut := [⟨45,216679842,216679967⟩,
⟨128,612699813,612700171⟩]
theorem checked20852 : checkPrefixCuts (2^48) 2737045505 9 Manual.Count131072.C020852.packed 128 cuts20852 = true := by
 decide +kernel
def pointBounds20852 : List (Nat × Nat × Nat) := [(2737091584,100561093147580,100561473832901)]
theorem point_links_checked20852 : (cuts20852.take 1).map (fun c => (2737045505-1+2*2^9*c.k,100560876467738+c.lower,100561257152934+c.upper)) = pointBounds20852 := by
 decide +kernel
def cuts20853 : List PrefixCut := [⟨1,5244535,5244537⟩,
⟨85,405982261,405982499⟩,
⟨128,616269476,616269836⟩]
theorem checked20853 : checkPrefixCuts (2^48) 2737176577 9 Manual.Count131072.C020853.packed 128 cuts20853 = true := by
 decide +kernel
def pointBounds20853 : List (Nat × Nat × Nat) := [(2737177600,100561494412086,100561875097642),(2737263616,100561895149812,100562275835604)]
theorem point_links_checked20853 : (cuts20853.take 2).map (fun c => (2737176577-1+2*2^9*c.k,100561489167551+c.lower,100561869853105+c.upper)) = pointBounds20853 := by
 decide +kernel
def cuts20854 : List PrefixCut := [⟨41,199589763,199589874⟩,
⟨125,604004127,604004472⟩,
⟨128,618399521,618399874⟩]
theorem checked20854 : checkPrefixCuts (2^48) 2737307649 9 Manual.Count131072.C020854.packed 128 cuts20854 = true := by
 decide +kernel
def pointBounds20854 : List (Nat × Nat × Nat) := [(2737349632,100562305026790,100562685712815),(2737435648,100562709441154,100563090127413)]
theorem point_links_checked20854 : (cuts20854.take 2).map (fun c => (2737307649-1+2*2^9*c.k,100562105437027+c.lower,100562486122941+c.upper)) = pointBounds20854 := by
 decide +kernel
def cuts20855 : List PrefixCut := [⟨81,401008217,401008445⟩,
⟨128,623613866,623614223⟩]
theorem checked20855 : checkPrefixCuts (2^48) 2737438721 9 Manual.Count131072.C020855.packed 128 cuts20855 = true := by
 decide +kernel
def pointBounds20855 : List (Nat × Nat × Nat) := [(2737521664,100563124844765,100563505531260)]
theorem point_links_checked20855 : (cuts20855.take 1).map (fun c => (2737438721-1+2*2^9*c.k,100562723836548+c.lower,100563104522815+c.upper)) = pointBounds20855 := by
 decide +kernel
def cuts20856 : List PrefixCut := [⟨37,181269110,181269218⟩,
⟨121,594898770,594899116⟩,
⟨128,628621915,628622281⟩]
theorem checked20856 : checkPrefixCuts (2^48) 2737569793 9 Manual.Count131072.C020856.packed 128 cuts20856 = true := by
 decide +kernel
def pointBounds20856 : List (Nat × Nat × Nat) := [(2737607680,100563528719524,100563909406256),(2737693696,100563942349184,100564323036154)]
theorem point_links_checked20856 : (cuts20856.take 2).map (fun c => (2737569793-1+2*2^9*c.k,100563347450414+c.lower,100563728137038+c.upper)) = pointBounds20856 := by
 decide +kernel
def cuts20857 : List PrefixCut := [⟨77,371257186,371257398⟩,
⟨128,615740302,615740658⟩]
theorem checked20857 : checkPrefixCuts (2^48) 2737700865 9 Manual.Count131072.C020857.packed 128 cuts20857 = true := by
 decide +kernel
def pointBounds20857 : List (Nat × Nat × Nat) := [(2737779712,100564347329515,100564728016717)]
theorem point_links_checked20857 : (cuts20857.take 1).map (fun c => (2737700865-1+2*2^9*c.k,100563976072329+c.lower,100564356759319+c.upper)) = pointBounds20857 := by
 decide +kernel
def cuts20858 : List PrefixCut := [⟨33,163054719,163054816⟩,
⟨117,573252770,573253111⟩,
⟨128,624963535,624963909⟩]
theorem checked20858 : checkPrefixCuts (2^48) 2737831937 9 Manual.Count131072.C020858.packed 128 cuts20858 = true := by
 decide +kernel
def pointBounds20858 : List (Nat × Nat × Nat) := [(2737865728,100564754867350,100565135554793),(2737951744,100565165065401,100565545753088)]
theorem point_links_checked20858 : (cuts20858.take 2).map (fun c => (2737831937-1+2*2^9*c.k,100564591812631+c.lower,100564972499977+c.upper)) = pointBounds20858 := by
 decide +kernel
def cuts20859 : List PrefixCut := [⟨73,351380952,351381155⟩,
⟨128,619690587,619690946⟩]
theorem checked20859 : checkPrefixCuts (2^48) 2737963009 9 Manual.Count131072.C020859.packed 128 cuts20859 = true := by
 decide +kernel
def pointBounds20859 : List (Nat × Nat × Nat) := [(2738037760,100565568157118,100565948845041)]
theorem point_links_checked20859 : (cuts20859.take 1).map (fun c => (2737963009-1+2*2^9*c.k,100565216776166+c.lower,100565597463886+c.upper)) = pointBounds20859 := by
 decide +kernel
def cuts20860 : List PrefixCut := [⟨29,143610215,143610296⟩,
⟨113,557367504,557367822⟩,
⟨128,630249116,630249479⟩]
theorem checked20860 : checkPrefixCuts (2^48) 2738094081 9 Manual.Count131072.C020860.packed 128 cuts20860 = true := by
 decide +kernel
def pointBounds20860 : List (Nat × Nat × Nat) := [(2738123776,100565980076968,100566360765128),(2738209792,100566393834257,100566774522654)]
theorem point_links_checked20860 : (cuts20860.take 2).map (fun c => (2738094081-1+2*2^9*c.k,100565836466753+c.lower,100566217154832+c.upper)) = pointBounds20860 := by
 decide +kernel
def cuts20861 : List PrefixCut := [⟨69,333153152,333153350⟩,
⟨128,619528520,619528890⟩]
theorem checked20861 : checkPrefixCuts (2^48) 2738225153 9 Manual.Count131072.C020861.packed 128 cuts20861 = true := by
 decide +kernel
def pointBounds20861 : List (Nat × Nat × Nat) := [(2738295808,100566799869021,100567180557661)]
theorem point_links_checked20861 : (cuts20861.take 1).map (fun c => (2738225153-1+2*2^9*c.k,100566466715869+c.lower,100566847404311+c.upper)) = pointBounds20861 := by
 decide +kernel
def cuts20862 : List PrefixCut := [⟨25,120880153,120880220⟩,
⟨109,519797071,519797372⟩,
⟨128,613948293,613948648⟩]
theorem checked20862 : checkPrefixCuts (2^48) 2738356225 9 Manual.Count131072.C020862.packed 128 cuts20862 = true := by
 decide +kernel
def pointBounds20862 : List (Nat × Nat × Nat) := [(2738381824,100567207124542,100567587813421),(2738467840,100567606041460,100567986730573)]
theorem point_links_checked20862 : (cuts20862.take 2).map (fun c => (2738356225-1+2*2^9*c.k,100567086244389+c.lower,100567466933201+c.upper)) = pointBounds20862 := by
 decide +kernel
def cuts20863 : List PrefixCut := [⟨65,316984577,316984756⟩,
⟨128,620291630,620291988⟩]
theorem checked20863 : checkPrefixCuts (2^48) 2738487297 9 Manual.Count131072.C020863.packed 128 cuts20863 = true := by
 decide +kernel
def pointBounds20863 : List (Nat × Nat × Nat) := [(2738553856,100568017177259,100568397866605)]
theorem point_links_checked20863 : (cuts20863.take 1).map (fun c => (2738487297-1+2*2^9*c.k,100567700192682+c.lower,100568080881849+c.upper)) = pointBounds20863 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000026
