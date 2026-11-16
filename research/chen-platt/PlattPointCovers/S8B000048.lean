import PlattPointSubsetKernel
import PlattPointPackets.S5B000122
import PlattPointPackets.S5B000123
import PlattPointPackets.S5B000124
import PlattPointPackets.S5B000125
import PlattPointPackets.S5B000126
import PlattPointPackets.S5B000127
import PlattPointPackets.S5B000128
import PlattPointPackets.S5B000129
import PlattPointPackets.S5B000130
import PlattPointPackets.S5B000131
import PlattPointPackets.S5B000132
import PlattPointPackets.S5B000133
import PlattGlobalGrid.S8B000048
namespace ChenEffective.PlattWindow.PointCovers.S8B000048
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((ChenEffective.PlattWindow.PointPackets.S5B000122.points ++ ChenEffective.PlattWindow.PointPackets.S5B000123.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000124.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000125.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000126.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000127.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000128.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000129.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000130.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000131.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000132.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000133.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000048.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000048.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000048
