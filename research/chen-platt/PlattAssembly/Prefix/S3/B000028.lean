import PlattAssemblyKernel
import PlattCertificates.Count131072.C020896
import PlattCertificates.Count131072.C020897
import PlattCertificates.Count131072.C020898
import PlattCertificates.Count131072.C020899
import PlattCertificates.Count131072.C020900
import PlattCertificates.Count131072.C020901
import PlattCertificates.Count131072.C020902
import PlattCertificates.Count131072.C020903
import PlattCertificates.Count131072.C020904
import PlattCertificates.Count131072.C020905
import PlattCertificates.Count131072.C020906
import PlattCertificates.Count131072.C020907
import PlattCertificates.Count131072.C020908
import PlattCertificates.Count131072.C020909
import PlattCertificates.Count131072.C020910
import PlattCertificates.Count131072.C020911
import PlattCertificates.Count131072.C020912
import PlattCertificates.Count131072.C020913
import PlattCertificates.Count131072.C020914
import PlattCertificates.Count131072.C020915
import PlattCertificates.Count131072.C020916
import PlattCertificates.Count131072.C020917
import PlattCertificates.Count131072.C020918
import PlattCertificates.Count131072.C020919
import PlattCertificates.Count131072.C020920
import PlattCertificates.Count131072.C020921
import PlattCertificates.Count131072.C020922
import PlattCertificates.Count131072.C020923
import PlattCertificates.Count131072.C020924
import PlattCertificates.Count131072.C020925
import PlattCertificates.Count131072.C020926
import PlattCertificates.Count131072.C020927
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000028
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts20896 : List PrefixCut := [⟨41,198470815,198470932⟩,
⟨125,602689155,602689504⟩,
⟨128,617363512,617363868⟩]
theorem checked20896 : checkPrefixCuts (2^48) 2742812673 9 Manual.Count131072.C020896.packed 128 cuts20896 = true := by
 decide +kernel
def pointBounds20896 : List (Nat × Nat × Nat) := [(2742854656,100588351615821,100588732316930),(2742940672,100588755834161,100589136535502)]
theorem point_links_checked20896 : (cuts20896.take 2).map (fun c => (2742812673-1+2*2^9*c.k,100588153145006+c.lower,100588533845998+c.upper)) = pointBounds20896 := by
 decide +kernel
def cuts20897 : List PrefixCut := [⟨81,394662175,394662408⟩,
⟨128,625440676,625441041⟩]
theorem checked20897 : checkPrefixCuts (2^48) 2742943745 9 Manual.Count131072.C020897.packed 128 cuts20897 = true := by
 decide +kernel
def pointBounds20897 : List (Nat × Nat × Nat) := [(2743026688,100589165170693,100589545872274)]
theorem point_links_checked20897 : (cuts20897.take 1).map (fun c => (2742943745-1+2*2^9*c.k,100588770508518+c.lower,100589151209866+c.upper)) = pointBounds20897 := by
 decide +kernel
def cuts20898 : List PrefixCut := [⟨37,176287773,176287874⟩,
⟨121,587240388,587240723⟩,
⟨128,621306292,621306648⟩]
theorem checked20898 : checkPrefixCuts (2^48) 2743074817 9 Manual.Count131072.C020898.packed 128 cuts20898 = true := by
 decide +kernel
def pointBounds20898 : List (Nat × Nat × Nat) := [(2743112704,100589572236967,100589952938781),(2743198720,100589983189582,100590363891630)]
theorem point_links_checked20898 : (cuts20898.take 2).map (fun c => (2743074817-1+2*2^9*c.k,100589395949194+c.lower,100589776650907+c.upper)) = pointBounds20898 := by
 decide +kernel
def cuts20899 : List PrefixCut := [⟨77,369075699,369075911⟩,
⟨128,615633268,615633621⟩]
theorem checked20899 : checkPrefixCuts (2^48) 2743205889 9 Manual.Count131072.C020899.packed 128 cuts20899 = true := by
 decide +kernel
def pointBounds20899 : List (Nat × Nat × Nat) := [(2743284736,100590386331185,100590767033466)]
theorem point_links_checked20899 : (cuts20899.take 1).map (fun c => (2743205889-1+2*2^9*c.k,100590017255486+c.lower,100590397957555+c.upper)) = pointBounds20899 := by
 decide +kernel
def cuts20900 : List PrefixCut := [⟨33,156468785,156468875⟩,
⟨117,565741184,565741511⟩,
⟨128,616629997,616630353⟩]
theorem checked20900 : checkPrefixCuts (2^48) 2743336961 9 Manual.Count131072.C020900.packed 128 cuts20900 = true := by
 decide +kernel
def pointBounds20900 : List (Nat × Nat × Nat) := [(2743370752,100590789357539,100591170060051),(2743456768,100591198629938,100591579332687)]
theorem point_links_checked20900 : (cuts20900.take 2).map (fun c => (2743336961-1+2*2^9*c.k,100590632888754+c.lower,100591013591176+c.upper)) = pointBounds20900 := by
 decide +kernel
def cuts20901 : List PrefixCut := [⟨73,345443378,345443582⟩,
⟨128,611060109,611060465⟩]
theorem checked20901 : checkPrefixCuts (2^48) 2743468033 9 Manual.Count131072.C020901.packed 128 cuts20901 = true := by
 decide +kernel
def pointBounds20901 : List (Nat × Nat × Nat) := [(2743542784,100591594962129,100591975665111)]
theorem point_links_checked20901 : (cuts20901.take 1).map (fun c => (2743468033-1+2*2^9*c.k,100591249518751+c.lower,100591630221529+c.upper)) = pointBounds20901 := by
 decide +kernel
def cuts20902 : List PrefixCut := [⟨29,137987255,137987335⟩,
⟨113,541783860,541784172⟩,
⟨128,611851940,611852295⟩]
theorem checked20902 : checkPrefixCuts (2^48) 2743599105 9 Manual.Count131072.C020902.packed 128 cuts20902 = true := by
 decide +kernel
def pointBounds20902 : List (Nat × Nat × Nat) := [(2743628800,100591998566115,100592379269329),(2743714816,100592402362720,100592783066166)]
theorem point_links_checked20902 : (cuts20902.take 2).map (fun c => (2743599105-1+2*2^9*c.k,100591860578860+c.lower,100592241281994+c.upper)) = pointBounds20902 := by
 decide +kernel
def cuts20903 : List PrefixCut := [⟨69,332074359,332074557⟩,
⟨128,612848499,612848857⟩]
theorem checked20903 : checkPrefixCuts (2^48) 2743730177 9 Manual.Count131072.C020903.packed 128 cuts20903 = true := by
 decide +kernel
def pointBounds20903 : List (Nat × Nat × Nat) := [(2743800832,100592804505159,100593185208846)]
theorem point_links_checked20903 : (cuts20903.take 1).map (fun c => (2743730177-1+2*2^9*c.k,100592472430800+c.lower,100592853134289+c.upper)) = pointBounds20903 := by
 decide +kernel
def cuts20904 : List PrefixCut := [⟨25,121971218,121971288⟩,
⟨109,526652989,526653291⟩,
⟨128,619897274,619897627⟩]
theorem checked20904 : checkPrefixCuts (2^48) 2743861249 9 Manual.Count131072.C020904.packed 128 cuts20904 = true := by
 decide +kernel
def pointBounds20904 : List (Nat × Nat × Nat) := [(2743886848,100593207250517,100593587954434),(2743972864,100593611932288,100593992636437)]
theorem point_links_checked20904 : (cuts20904.take 2).map (fun c => (2743861249-1+2*2^9*c.k,100593085279299+c.lower,100593465983146+c.upper)) = pointBounds20904 := by
 decide +kernel
def cuts20905 : List PrefixCut := [⟨65,313271296,313271478⟩,
⟨128,615764633,615764993⟩]
theorem checked20905 : checkPrefixCuts (2^48) 2743992321 9 Manual.Count131072.C020905.packed 128 cuts20905 = true := by
 decide +kernel
def pointBounds20905 : List (Nat × Nat × Nat) := [(2744058880,100594018447869,100594399152251)]
theorem point_links_checked20905 : (cuts20905.take 1).map (fun c => (2743992321-1+2*2^9*c.k,100593705176573+c.lower,100594085880773+c.upper)) = pointBounds20905 := by
 decide +kernel
def cuts20906 : List PrefixCut := [⟨21,100316684,100316745⟩,
⟨105,502601279,502601570⟩,
⟨128,615324894,615325253⟩]
theorem checked20906 : checkPrefixCuts (2^48) 2744123393 9 Manual.Count131072.C020906.packed 128 cuts20906 = true := by
 decide +kernel
def pointBounds20906 : List (Nat × Nat × Nat) := [(2744144896,100594421257890,100594801962511),(2744230912,100594823542485,100595204247336)]
theorem point_links_checked20906 : (cuts20906.take 2).map (fun c => (2744123393-1+2*2^9*c.k,100594320941206+c.lower,100594701645766+c.upper)) = pointBounds20906 := by
 decide +kernel
def cuts20907 : List PrefixCut := [⟨61,298984631,298984810⟩,
⟨128,617962339,617962703⟩]
theorem checked20907 : checkPrefixCuts (2^48) 2744254465 9 Manual.Count131072.C020907.packed 128 cuts20907 = true := by
 decide +kernel
def pointBounds20907 : List (Nat × Nat × Nat) := [(2744316928,100595235250731,100595615955829)]
theorem point_links_checked20907 : (cuts20907.take 1).map (fun c => (2744254465-1+2*2^9*c.k,100594936266100+c.lower,100595316971019+c.upper)) = pointBounds20907 := by
 decide +kernel
def cuts20908 : List PrefixCut := [⟨17,80922662,80922710⟩,
⟨101,481733499,481733782⟩,
⟨128,612907139,612907497⟩]
theorem checked20908 : checkPrefixCuts (2^48) 2744385537 9 Manual.Count131072.C020908.packed 128 cuts20908 = true := by
 decide +kernel
def pointBounds20908 : List (Nat × Nat × Nat) := [(2744402944,100595635151101,100596015856432),(2744488960,100596035961938,100596416667504)]
theorem point_links_checked20908 : (cuts20908.take 2).map (fun c => (2744385537-1+2*2^9*c.k,100595554228439+c.lower,100595934933722+c.upper)) = pointBounds20908 := by
 decide +kernel
def cuts20909 : List PrefixCut := [⟨57,273214270,273214429⟩,
⟨128,618108332,618108693⟩]
theorem checked20909 : checkPrefixCuts (2^48) 2744516609 9 Manual.Count131072.C020909.packed 128 cuts20909 = true := by
 decide +kernel
def pointBounds20909 : List (Nat × Nat × Nat) := [(2744574976,100596440349848,100596821055648)]
theorem point_links_checked20909 : (cuts20909.take 1).map (fun c => (2744516609-1+2*2^9*c.k,100596167135578+c.lower,100596547841219+c.upper)) = pointBounds20909 := by
 decide +kernel
def cuts20910 : List PrefixCut := [⟨13,65019151,65019189⟩,
⟨97,471842982,471843257⟩,
⟨128,621873327,621873692⟩]
theorem checked20910 : checkPrefixCuts (2^48) 2744647681 9 Manual.Count131072.C020910.packed 128 cuts20910 = true := by
 decide +kernel
def pointBounds20910 : List (Nat × Nat × Nat) := [(2744660992,100596850263061,100597230969101),(2744747008,100597257086892,100597637793169)]
theorem point_links_checked20910 : (cuts20910.take 2).map (fun c => (2744647681-1+2*2^9*c.k,100596785243910+c.lower,100597165949912+c.upper)) = pointBounds20910 := by
 decide +kernel
def cuts20911 : List PrefixCut := [⟨53,253806753,253806898⟩,
⟨128,617741603,617741957⟩]
theorem checked20911 : checkPrefixCuts (2^48) 2744778753 9 Manual.Count131072.C020911.packed 128 cuts20911 = true := by
 decide +kernel
def pointBounds20911 : List (Nat × Nat × Nat) := [(2744833024,100597660923990,100598041630502)]
theorem point_links_checked20911 : (cuts20911.take 1).map (fun c => (2744778753-1+2*2^9*c.k,100597407117237+c.lower,100597787823604+c.upper)) = pointBounds20911 := by
 decide +kernel
def cuts20912 : List PrefixCut := [⟨9,45016875,45016902⟩,
⟨93,450982116,450982378⟩,
⟨128,622839268,622839633⟩]
theorem checked20912 : checkPrefixCuts (2^48) 2744909825 9 Manual.Count131072.C020912.packed 128 cuts20912 = true := by
 decide +kernel
def pointBounds20912 : List (Nat × Nat × Nat) := [(2744919040,100598069875715,100598450582463),(2745005056,100598475840956,100598856547939)]
theorem point_links_checked20912 : (cuts20912.take 2).map (fun c => (2744909825-1+2*2^9*c.k,100598024858840+c.lower,100598405565561+c.upper)) = pointBounds20912 := by
 decide +kernel
def cuts20913 : List PrefixCut := [⟨49,235120738,235120876⟩,
⟨128,624449992,624450355⟩]
theorem checked20913 : checkPrefixCuts (2^48) 2745040897 9 Manual.Count131072.C020913.packed 128 cuts20913 = true := by
 decide +kernel
def pointBounds20913 : List (Nat × Nat × Nat) := [(2745091072,100598882818846,100599263526070)]
theorem point_links_checked20913 : (cuts20913.take 1).map (fun c => (2745040897-1+2*2^9*c.k,100598647698108+c.lower,100599028405194+c.upper)) = pointBounds20913 := by
 decide +kernel
def cuts20914 : List PrefixCut := [⟨5,23582918,23582931⟩,
⟨89,433303688,433303937⟩,
⟨128,624625373,624625729⟩]
theorem checked20914 : checkPrefixCuts (2^48) 2745171969 9 Manual.Count131072.C020914.packed 128 cuts20914 = true := by
 decide +kernel
def pointBounds20914 : List (Nat × Nat × Nat) := [(2745177088,100599295731018,100599676438480),(2745263104,100599705451788,100600086159486)]
theorem point_links_checked20914 : (cuts20914.take 2).map (fun c => (2745171969-1+2*2^9*c.k,100599272148100+c.lower,100599652855549+c.upper)) = pointBounds20914 := by
 decide +kernel
def cuts20915 : List PrefixCut := [⟨45,217360998,217361127⟩,
⟨128,611779823,611780189⟩]
theorem checked20915 : checkPrefixCuts (2^48) 2745303041 9 Manual.Count131072.C020915.packed 128 cuts20915 = true := by
 decide +kernel
def pointBounds20915 : List (Nat × Nat × Nat) := [(2745349120,100600114134471,100600494842405)]
theorem point_links_checked20915 : (cuts20915.take 1).map (fun c => (2745303041-1+2*2^9*c.k,100599896773473+c.lower,100600277481278+c.upper)) = pointBounds20915 := by
 decide +kernel
def cuts20916 : List PrefixCut := [⟨1,4818661,4818664⟩,
⟨85,409272298,409272539⟩,
⟨128,615133773,615134136⟩]
theorem checked20916 : checkPrefixCuts (2^48) 2745434113 9 Manual.Count131072.C020916.packed 128 cuts20916 = true := by
 decide +kernel
def pointBounds20916 : List (Nat × Nat × Nat) := [(2745435136,100600513371957,100600894080131),(2745521152,100600917825594,100601298534006)]
theorem point_links_checked20916 : (cuts20916.take 2).map (fun c => (2745434113-1+2*2^9*c.k,100600508553296+c.lower,100600889261467+c.upper)) = pointBounds20916 := by
 decide +kernel
def cuts20917 : List PrefixCut := [⟨41,202065066,202065184⟩,
⟨125,604032856,604033211⟩,
⟨128,617154775,617155139⟩]
theorem checked20917 : checkPrefixCuts (2^48) 2745565185 9 Manual.Count131072.C020917.packed 128 cuts20917 = true := by
 decide +kernel
def pointBounds20917 : List (Nat × Nat × Nat) := [(2745607168,100601325752135,100601706460787),(2745693184,100601727719925,100602108428814)]
theorem point_links_checked20917 : (cuts20917.take 2).map (fun c => (2745565185-1+2*2^9*c.k,100601123687069+c.lower,100601504395603+c.upper)) = pointBounds20917 := by
 decide +kernel
def cuts20918 : List PrefixCut := [⟨81,394164012,394164241⟩,
⟨128,615382636,615382993⟩]
theorem checked20918 : checkPrefixCuts (2^48) 2745696257 9 Manual.Count131072.C020918.packed 128 cuts20918 = true := by
 decide +kernel
def pointBounds20918 : List (Nat × Nat × Nat) := [(2745779200,100602135005856,100602515714983)]
theorem point_links_checked20918 : (cuts20918.take 1).map (fun c => (2745696257-1+2*2^9*c.k,100601740841844+c.lower,100602121550742+c.upper)) = pointBounds20918 := by
 decide +kernel
def cuts20919 : List PrefixCut := [⟨37,179083823,179083927⟩,
⟨121,579783807,579784145⟩,
⟨128,612688004,612688362⟩]
theorem checked20919 : checkPrefixCuts (2^48) 2745827329 9 Manual.Count131072.C020919.packed 128 cuts20919 = true := by
 decide +kernel
def pointBounds20919 : List (Nat × Nat × Nat) := [(2745865216,100602535308303,100602916017662),(2745951232,100602936008287,100603316717880)]
theorem point_links_checked20919 : (cuts20919.take 2).map (fun c => (2745827329-1+2*2^9*c.k,100602356224480+c.lower,100602736933735+c.upper)) = pointBounds20919 := by
 decide +kernel
def cuts20920 : List PrefixCut := [⟨77,373420929,373421150⟩,
⟨128,629264045,629264415⟩]
theorem checked20920 : checkPrefixCuts (2^48) 2745958401 9 Manual.Count131072.C020920.packed 128 cuts20920 = true := by
 decide +kernel
def pointBounds20920 : List (Nat × Nat × Nat) := [(2746037248,100603342333413,100603723043247)]
theorem point_links_checked20920 : (cuts20920.take 1).map (fun c => (2745958401-1+2*2^9*c.k,100602968912484+c.lower,100603349622097+c.upper)) = pointBounds20920 := by
 decide +kernel
def cuts20921 : List PrefixCut := [⟨33,158874437,158874529⟩,
⟨117,567839099,567839426⟩,
⟨128,620214343,620214700⟩]
theorem checked20921 : checkPrefixCuts (2^48) 2746089473 9 Manual.Count131072.C020921.packed 128 cuts20921 = true := by
 decide +kernel
def pointBounds20921 : List (Nat × Nat × Nat) := [(2746123264,100603757050966,100604137761041),(2746209280,100604166015628,100604546725938)]
theorem point_links_checked20921 : (cuts20921.take 2).map (fun c => (2746089473-1+2*2^9*c.k,100603598176529+c.lower,100603978886512+c.upper)) = pointBounds20921 := by
 decide +kernel
def cuts20922 : List PrefixCut := [⟨73,348684460,348684666⟩,
⟨128,616597334,616597691⟩]
theorem checked20922 : checkPrefixCuts (2^48) 2746220545 9 Manual.Count131072.C020922.packed 128 cuts20922 = true := by
 decide +kernel
def pointBounds20922 : List (Nat × Nat × Nat) := [(2746295296,100604567075332,100604947785878)]
theorem point_links_checked20922 : (cuts20922.take 1).map (fun c => (2746220545-1+2*2^9*c.k,100604218390872+c.lower,100604599101212+c.upper)) = pointBounds20922 := by
 decide +kernel
def cuts20923 : List PrefixCut := [⟨29,139898752,139898828⟩,
⟨113,540933342,540933653⟩,
⟨128,613390860,613391211⟩]
theorem checked20923 : checkPrefixCuts (2^48) 2746351617 9 Manual.Count131072.C020923.packed 128 cuts20923 = true := by
 decide +kernel
def pointBounds20923 : List (Nat × Nat × Nat) := [(2746381312,100604974886958,100605355597731),(2746467328,100605375921548,100605756632556)]
theorem point_links_checked20923 : (cuts20923.take 2).map (fun c => (2746351617-1+2*2^9*c.k,100604834988206+c.lower,100605215698903+c.upper)) = pointBounds20923 := by
 decide +kernel
def cuts20924 : List PrefixCut := [⟨69,332459005,332459200⟩,
⟨128,621150358,621150719⟩]
theorem checked20924 : checkPrefixCuts (2^48) 2746482689 9 Manual.Count131072.C020924.packed 128 cuts20924 = true := by
 decide +kernel
def pointBounds20924 : List (Nat × Nat × Nat) := [(2746553344,100605780838071,100606161549314)]
theorem point_links_checked20924 : (cuts20924.take 1).map (fun c => (2746482689-1+2*2^9*c.k,100605448379066+c.lower,100605829090114+c.upper)) = pointBounds20924 := by
 decide +kernel
def cuts20925 : List PrefixCut := [⟨25,121029145,121029218⟩,
⟨109,527252434,527252744⟩,
⟨128,615074512,615074873⟩]
theorem checked20925 : checkPrefixCuts (2^48) 2746613761 9 Manual.Count131072.C020925.packed 128 cuts20925 = true := by
 decide +kernel
def pointBounds20925 : List (Nat × Nat × Nat) := [(2746639360,100606190558569,100606571270051),(2746725376,100606596781858,100606977493577)]
theorem point_links_checked20925 : (cuts20925.take 2).map (fun c => (2746613761-1+2*2^9*c.k,100606069529424+c.lower,100606450240833+c.upper)) = pointBounds20925 := by
 decide +kernel
def cuts20926 : List PrefixCut := [⟨65,317876125,317876308⟩,
⟨128,625702378,625702739⟩]
theorem checked20926 : checkPrefixCuts (2^48) 2746744833 9 Manual.Count131072.C020926.packed 128 cuts20926 = true := by
 decide +kernel
def pointBounds20926 : List (Nat × Nat × Nat) := [(2746811392,100607002480061,100607383192014)]
theorem point_links_checked20926 : (cuts20926.take 1).map (fun c => (2746744833-1+2*2^9*c.k,100606684603936+c.lower,100607065315706+c.upper)) = pointBounds20926 := by
 decide +kernel
def cuts20927 : List PrefixCut := [⟨21,100318635,100318693⟩,
⟨105,498306391,498306681⟩,
⟨128,610609633,610609987⟩]
theorem checked20927 : checkPrefixCuts (2^48) 2746875905 9 Manual.Count131072.C020927.packed 128 cuts20927 = true := by
 decide +kernel
def pointBounds20927 : List (Nat × Nat × Nat) := [(2746897408,100607410624949,100607791337138),(2746983424,100607808612705,100608189325126)]
theorem point_links_checked20927 : (cuts20927.take 2).map (fun c => (2746875905-1+2*2^9*c.k,100607310306314+c.lower,100607691018445+c.upper)) = pointBounds20927 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000028
