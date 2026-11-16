import PlattAssemblyKernel
import PlattCertificates.Count131072.C039824
import PlattCertificates.Count131072.C039825
import PlattCertificates.Count131072.C039826
import PlattCertificates.Count131072.C039827
import PlattCertificates.Count131072.C039828
import PlattCertificates.Count131072.C039829
import PlattCertificates.Count131072.C039830
import PlattCertificates.Count131072.C039831
import PlattCertificates.Count131072.C039832
import PlattCertificates.Count131072.C039833
import PlattCertificates.Count131072.C039834
import PlattCertificates.Count131072.C039835
import PlattCertificates.Count131072.C039836
import PlattCertificates.Count131072.C039837
import PlattCertificates.Count131072.C039838
import PlattCertificates.Count131072.C039839
import PlattCertificates.Count131072.C039840
import PlattCertificates.Count131072.C039841
import PlattCertificates.Count131072.C039842
import PlattCertificates.Count131072.C039843
import PlattCertificates.Count131072.C039844
import PlattCertificates.Count131072.C039845
import PlattCertificates.Count131072.C039846
import PlattCertificates.Count131072.C039847
import PlattCertificates.Count131072.C039848
import PlattCertificates.Count131072.C039849
import PlattCertificates.Count131072.C039850
import PlattCertificates.Count131072.C039851
import PlattCertificates.Count131072.C039852
import PlattCertificates.Count131072.C039853
import PlattCertificates.Count131072.C039854
import PlattCertificates.Count131072.C039855
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000307
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts39824 : List PrefixCut := [⟨64,314892711,314892898⟩]
theorem checked39824 : checkPrefixCuts (2^48) 5223743489 10 Manual.Count131072.C039824.packed 64 cuts39824 = true := by
 decide +kernel
def cuts39825 : List PrefixCut := [⟨4,17888942,17888953⟩,
⟨64,312082931,312083118⟩]
theorem checked39825 : checkPrefixCuts (2^48) 5223874561 10 Manual.Count131072.C039825.packed 64 cuts39825 = true := by
 decide +kernel
def pointBounds39825 : List (Nat × Nat × Nat) := [(5223882752,108811136612233,108811522085125)]
theorem point_links_checked39825 : (cuts39825.take 1).map (fun c => (5223874561-1+2*2^10*c.k,108811118723291+c.lower,108811504196172+c.upper)) = pointBounds39825 := by
 decide +kernel
def cuts39826 : List PrefixCut := [⟨20,100326122,100326180⟩,
⟨64,319618365,319618557⟩]
theorem checked39826 : checkPrefixCuts (2^48) 5224005633 10 Manual.Count131072.C039826.packed 64 cuts39826 = true := by
 decide +kernel
def pointBounds39826 : List (Nat × Nat × Nat) := [(5224046592,108811531132344,108811916605470)]
theorem point_links_checked39826 : (cuts39826.take 1).map (fun c => (5224005633-1+2*2^10*c.k,108811430806222+c.lower,108811816279290+c.upper)) = pointBounds39826 := by
 decide +kernel
def cuts39827 : List PrefixCut := [⟨36,178933203,178933309⟩,
⟨64,316162094,316162278⟩]
theorem checked39827 : checkPrefixCuts (2^48) 5224136705 10 Manual.Count131072.C039827.packed 64 cuts39827 = true := by
 decide +kernel
def pointBounds39827 : List (Nat × Nat × Nat) := [(5224210432,108811929357790,108812314831156)]
theorem point_links_checked39827 : (cuts39827.take 1).map (fun c => (5224136705-1+2*2^10*c.k,108811750424587+c.lower,108812135897847+c.upper)) = pointBounds39827 := by
 decide +kernel
def cuts39828 : List PrefixCut := [⟨52,255434636,255434789⟩,
⟨64,314537834,314538021⟩]
theorem checked39828 : checkPrefixCuts (2^48) 5224267777 10 Manual.Count131072.C039828.packed 64 cuts39828 = true := by
 decide +kernel
def pointBounds39828 : List (Nat × Nat × Nat) := [(5224374272,108812322021317,108812707494914)]
theorem point_links_checked39828 : (cuts39828.take 1).map (fun c => (5224267777-1+2*2^10*c.k,108812066586681+c.lower,108812452060125+c.upper)) = pointBounds39828 := by
 decide +kernel
def cuts39829 : List PrefixCut := [⟨64,317008255,317008442⟩]
theorem checked39829 : checkPrefixCuts (2^48) 5224398849 10 Manual.Count131072.C039829.packed 64 cuts39829 = true := by
 decide +kernel
def cuts39830 : List PrefixCut := [⟨4,19718469,19718480⟩,
⟨64,319478550,319478739⟩]
theorem checked39830 : checkPrefixCuts (2^48) 5224529921 10 Manual.Count131072.C039830.packed 64 cuts39830 = true := by
 decide +kernel
def pointBounds39830 : List (Nat × Nat × Nat) := [(5224538112,108812717851239,108813103325068)]
theorem point_links_checked39830 : (cuts39830.take 1).map (fun c => (5224529921-1+2*2^10*c.k,108812698132770+c.lower,108813083606588+c.upper)) = pointBounds39830 := by
 decide +kernel
def cuts39831 : List PrefixCut := [⟨20,98858934,98858995⟩,
⟨64,313921547,313921739⟩]
theorem checked39831 : checkPrefixCuts (2^48) 5224660993 10 Manual.Count131072.C039831.packed 64 cuts39831 = true := by
 decide +kernel
def pointBounds39831 : List (Nat × Nat × Nat) := [(5224701952,108813116470254,108813501944322)]
theorem point_links_checked39831 : (cuts39831.take 1).map (fun c => (5224660993-1+2*2^10*c.k,108813017611320+c.lower,108813403085327+c.upper)) = pointBounds39831 := by
 decide +kernel
def cuts39832 : List PrefixCut := [⟨36,174978067,174978171⟩,
⟨64,310519720,310519906⟩]
theorem checked39832 : checkPrefixCuts (2^48) 5224792065 10 Manual.Count131072.C039832.packed 64 cuts39832 = true := by
 decide +kernel
def pointBounds39832 : List (Nat × Nat × Nat) := [(5224865792,108813506510934,108813891985237)]
theorem point_links_checked39832 : (cuts39832.take 1).map (fun c => (5224792065-1+2*2^10*c.k,108813331532867+c.lower,108813717007066+c.upper)) = pointBounds39832 := by
 decide +kernel
def cuts39833 : List PrefixCut := [⟨52,255187101,255187257⟩,
⟨64,313582572,313582763⟩]
theorem checked39833 : checkPrefixCuts (2^48) 5224923137 10 Manual.Count131072.C039833.packed 64 cuts39833 = true := by
 decide +kernel
def pointBounds39833 : List (Nat × Nat × Nat) := [(5225029632,108813897239688,108814282714229)]
theorem point_links_checked39833 : (cuts39833.take 1).map (fun c => (5224923137-1+2*2^10*c.k,108813642052587+c.lower,108814027526972+c.upper)) = pointBounds39833 := by
 decide +kernel
def cuts39834 : List PrefixCut := [⟨64,320092935,320093114⟩]
theorem checked39834 : checkPrefixCuts (2^48) 5225054209 10 Manual.Count131072.C039834.packed 64 cuts39834 = true := by
 decide +kernel
def cuts39835 : List PrefixCut := [⟨4,19662127,19662138⟩,
⟨64,314913493,314913680⟩]
theorem checked39835 : checkPrefixCuts (2^48) 5225185281 10 Manual.Count131072.C039835.packed 64 cuts39835 = true := by
 decide +kernel
def pointBounds39835 : List (Nat × Nat × Nat) := [(5225193472,108814295390221,108814680864987)]
theorem point_links_checked39835 : (cuts39835.take 1).map (fun c => (5225185281-1+2*2^10*c.k,108814275728094+c.lower,108814661202849+c.upper)) = pointBounds39835 := by
 decide +kernel
def cuts39836 : List PrefixCut := [⟨20,97499849,97499910⟩,
⟨64,314474679,314474869⟩]
theorem checked39836 : checkPrefixCuts (2^48) 5225316353 10 Manual.Count131072.C039836.packed 64 cuts39836 = true := by
 decide +kernel
def pointBounds39836 : List (Nat × Nat × Nat) := [(5225357312,108814688141436,108815073616439)]
theorem point_links_checked39836 : (cuts39836.take 1).map (fun c => (5225316353-1+2*2^10*c.k,108814590641587+c.lower,108814976116529+c.upper)) = pointBounds39836 := by
 decide +kernel
def cuts39837 : List PrefixCut := [⟨36,179103792,179103897⟩,
⟨64,313120218,313120402⟩]
theorem checked39837 : checkPrefixCuts (2^48) 5225447425 10 Manual.Count131072.C039837.packed 64 cuts39837 = true := by
 decide +kernel
def pointBounds39837 : List (Nat × Nat × Nat) := [(5225521152,108815084220058,108815469695295)]
theorem point_links_checked39837 : (cuts39837.take 1).map (fun c => (5225447425-1+2*2^10*c.k,108814905116266+c.lower,108815290591398+c.upper)) = pointBounds39837 := by
 decide +kernel
def cuts39838 : List PrefixCut := [⟨52,255963066,255963218⟩,
⟨64,314835987,314836173⟩]
theorem checked39838 : checkPrefixCuts (2^48) 5225578497 10 Manual.Count131072.C039838.packed 64 cuts39838 = true := by
 decide +kernel
def pointBounds39838 : List (Nat × Nat × Nat) := [(5225684992,108815474199550,108815859675018)]
theorem point_links_checked39838 : (cuts39838.take 1).map (fun c => (5225578497-1+2*2^10*c.k,108815218236484+c.lower,108815603711800+c.upper)) = pointBounds39838 := by
 decide +kernel
def cuts39839 : List PrefixCut := [⟨64,319190971,319191163⟩]
theorem checked39839 : checkPrefixCuts (2^48) 5225709569 10 Manual.Count131072.C039839.packed 64 cuts39839 = true := by
 decide +kernel
def cuts39840 : List PrefixCut := [⟨4,20467592,20467605⟩,
⟨64,319452245,319452435⟩]
theorem checked39840 : checkPrefixCuts (2^48) 5225840641 10 Manual.Count131072.C039840.packed 64 cuts39840 = true := by
 decide +kernel
def pointBounds39840 : List (Nat × Nat × Nat) := [(5225848832,108815872731034,108816258206741)]
theorem point_links_checked39840 : (cuts39840.take 1).map (fun c => (5225840641-1+2*2^10*c.k,108815852263442+c.lower,108816237739136+c.upper)) = pointBounds39840 := by
 decide +kernel
def cuts39841 : List PrefixCut := [⟨20,97972368,97972424⟩,
⟨64,313681218,313681406⟩]
theorem checked39841 : checkPrefixCuts (2^48) 5225971713 10 Manual.Count131072.C039841.packed 64 cuts39841 = true := by
 decide +kernel
def pointBounds39841 : List (Nat × Nat × Nat) := [(5226012672,108816269688055,108816655163995)]
theorem point_links_checked39841 : (cuts39841.take 1).map (fun c => (5225971713-1+2*2^10*c.k,108816171715687+c.lower,108816557191571+c.upper)) = pointBounds39841 := by
 decide +kernel
def cuts39842 : List PrefixCut := [⟨36,178704322,178704425⟩,
⟨64,314589005,314589185⟩]
theorem checked39842 : checkPrefixCuts (2^48) 5226102785 10 Manual.Count131072.C039842.packed 64 cuts39842 = true := by
 decide +kernel
def pointBounds39842 : List (Nat × Nat × Nat) := [(5226176512,108816664101227,108817049577402)]
theorem point_links_checked39842 : (cuts39842.take 1).map (fun c => (5226102785-1+2*2^10*c.k,108816485396905+c.lower,108816870872977+c.upper)) = pointBounds39842 := by
 decide +kernel
def cuts39843 : List PrefixCut := [⟨52,264871296,264871452⟩,
⟨64,323521406,323521598⟩]
theorem checked39843 : checkPrefixCuts (2^48) 5226233857 10 Manual.Count131072.C039843.packed 64 cuts39843 = true := by
 decide +kernel
def pointBounds39843 : List (Nat × Nat × Nat) := [(5226340352,108817064857206,108817450333614)]
theorem point_links_checked39843 : (cuts39843.take 1).map (fun c => (5226233857-1+2*2^10*c.k,108816799985910+c.lower,108817185462162+c.upper)) = pointBounds39843 := by
 decide +kernel
def cuts39844 : List PrefixCut := [⟨64,315327149,315327340⟩]
theorem checked39844 : checkPrefixCuts (2^48) 5226364929 10 Manual.Count131072.C039844.packed 64 cuts39844 = true := by
 decide +kernel
def cuts39845 : List PrefixCut := [⟨4,20303459,20303471⟩,
⟨64,311172474,311172657⟩]
theorem checked39845 : checkPrefixCuts (2^48) 5226496001 10 Manual.Count131072.C039845.packed 64 cuts39845 = true := by
 decide +kernel
def pointBounds39845 : List (Nat × Nat × Nat) := [(5226504192,108817459137924,108817844614571)]
theorem point_links_checked39845 : (cuts39845.take 1).map (fun c => (5226496001-1+2*2^10*c.k,108817438834465+c.lower,108817824311100+c.upper)) = pointBounds39845 := by
 decide +kernel
def cuts39846 : List PrefixCut := [⟨20,96667596,96667652⟩,
⟨64,311110794,311110980⟩]
theorem checked39846 : checkPrefixCuts (2^48) 5226627073 10 Manual.Count131072.C039846.packed 64 cuts39846 = true := by
 decide +kernel
def pointBounds39846 : List (Nat × Nat × Nat) := [(5226668032,108817846674535,108818232151409)]
theorem point_links_checked39846 : (cuts39846.take 1).map (fun c => (5226627073-1+2*2^10*c.k,108817750006939+c.lower,108818135483757+c.upper)) = pointBounds39846 := by
 decide +kernel
def cuts39847 : List PrefixCut := [⟨36,176904796,176904901⟩,
⟨64,313257087,313257274⟩]
theorem checked39847 : checkPrefixCuts (2^48) 5226758145 10 Manual.Count131072.C039847.packed 64 cuts39847 = true := by
 decide +kernel
def pointBounds39847 : List (Nat × Nat × Nat) := [(5226831872,108818238022529,108818623499638)]
theorem point_links_checked39847 : (cuts39847.take 1).map (fun c => (5226758145-1+2*2^10*c.k,108818061117733+c.lower,108818446594737+c.upper)) = pointBounds39847 := by
 decide +kernel
def cuts39848 : List PrefixCut := [⟨52,253798688,253798839⟩,
⟨64,312710696,312710883⟩]
theorem checked39848 : checkPrefixCuts (2^48) 5226889217 10 Manual.Count131072.C039848.packed 64 cuts39848 = true := by
 decide +kernel
def pointBounds39848 : List (Nat × Nat × Nat) := [(5226995712,108818628173508,108819013650850)]
theorem point_links_checked39848 : (cuts39848.take 1).map (fun c => (5226889217-1+2*2^10*c.k,108818374374820+c.lower,108818759852011+c.upper)) = pointBounds39848 := by
 decide +kernel
def cuts39849 : List PrefixCut := [⟨64,317926251,317926440⟩]
theorem checked39849 : checkPrefixCuts (2^48) 5227020289 10 Manual.Count131072.C039849.packed 64 cuts39849 = true := by
 decide +kernel
def cuts39850 : List PrefixCut := [⟨4,18954700,18954711⟩,
⟨64,313395075,313395260⟩]
theorem checked39850 : checkPrefixCuts (2^48) 5227151361 10 Manual.Count131072.C039850.packed 64 cuts39850 = true := by
 decide +kernel
def pointBounds39850 : List (Nat × Nat × Nat) := [(5227159552,108819023966467,108819409444045)]
theorem point_links_checked39850 : (cuts39850.take 1).map (fun c => (5227151361-1+2*2^10*c.k,108819005011767+c.lower,108819390489334+c.upper)) = pointBounds39850 := by
 decide +kernel
def cuts39851 : List PrefixCut := [⟨20,99778607,99778663⟩,
⟨64,317371833,317372017⟩]
theorem checked39851 : checkPrefixCuts (2^48) 5227282433 10 Manual.Count131072.C039851.packed 64 cuts39851 = true := by
 decide +kernel
def pointBounds39851 : List (Nat × Nat × Nat) := [(5227323392,108819418185449,108819803663257)]
theorem point_links_checked39851 : (cuts39851.take 1).map (fun c => (5227282433-1+2*2^10*c.k,108819318406842+c.lower,108819703884594+c.upper)) = pointBounds39851 := by
 decide +kernel
def cuts39852 : List PrefixCut := [⟨36,178282599,178282703⟩,
⟨64,315963913,315964101⟩]
theorem checked39852 : checkPrefixCuts (2^48) 5227413505 10 Manual.Count131072.C039852.packed 64 cuts39852 = true := by
 decide +kernel
def pointBounds39852 : List (Nat × Nat × Nat) := [(5227487232,108819814061274,108820199539314)]
theorem point_links_checked39852 : (cuts39852.take 1).map (fun c => (5227413505-1+2*2^10*c.k,108819635778675+c.lower,108820021256611+c.upper)) = pointBounds39852 := by
 decide +kernel
def cuts39853 : List PrefixCut := [⟨52,256997529,256997681⟩,
⟨64,316063678,316063866⟩]
theorem checked39853 : checkPrefixCuts (2^48) 5227544577 10 Manual.Count131072.C039853.packed 64 cuts39853 = true := by
 decide +kernel
def pointBounds39853 : List (Nat × Nat × Nat) := [(5227651072,108820208740117,108820594218393)]
theorem point_links_checked39853 : (cuts39853.take 1).map (fun c => (5227544577-1+2*2^10*c.k,108819951742588+c.lower,108820337220712+c.upper)) = pointBounds39853 := by
 decide +kernel
def cuts39854 : List PrefixCut := [⟨64,315517303,315517488⟩]
theorem checked39854 : checkPrefixCuts (2^48) 5227675649 10 Manual.Count131072.C039854.packed 64 cuts39854 = true := by
 decide +kernel
def cuts39855 : List PrefixCut := [⟨4,18683114,18683125⟩,
⟨64,309586874,309587058⟩]
theorem checked39855 : checkPrefixCuts (2^48) 5227806721 10 Manual.Count131072.C039855.packed 64 cuts39855 = true := by
 decide +kernel
def pointBounds39855 : List (Nat × Nat × Nat) := [(5227814912,108820602006683,108820987485191)]
theorem point_links_checked39855 : (cuts39855.take 1).map (fun c => (5227806721-1+2*2^10*c.k,108820583323569+c.lower,108820968802066+c.upper)) = pointBounds39855 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000307
