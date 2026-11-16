import PlattPointSubsetKernel
import PlattPointPackets.S7B000033
import PlattPointPackets.S7B000034
import PlattPointPackets.S7B000035
import PlattPointPackets.S7B000036
import PlattPointPackets.S7B000037
import PlattPointPackets.S7B000038
import PlattPointPackets.S7B000039
import PlattPointPackets.S7B000040
import PlattPointPackets.S7B000041
import PlattPointPackets.S7B000042
import PlattPointPackets.S7B000043
import PlattPointPackets.S7B000044
import PlattPointPackets.S7B000045
import PlattPointPackets.S7B000046
import PlattPointPackets.S7B000047
import PlattPointPackets.S7B000048
import PlattGlobalGrid.S8B000089
namespace ChenEffective.PlattWindow.PointCovers.S8B000089
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((((((ChenEffective.PlattWindow.PointPackets.S7B000033.points ++ ChenEffective.PlattWindow.PointPackets.S7B000034.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000035.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000036.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000037.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000038.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000039.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000040.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000041.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000042.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000043.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000044.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000045.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000046.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000047.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000048.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000089.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000089.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000089
