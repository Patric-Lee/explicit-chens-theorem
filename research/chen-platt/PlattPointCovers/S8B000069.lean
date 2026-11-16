import PlattPointSubsetKernel
import PlattPointPackets.S6B000062
import PlattPointPackets.S6B000063
import PlattPointPackets.S6B000064
import PlattPointPackets.S6B000065
import PlattPointPackets.S6B000066
import PlattPointPackets.S6B000067
import PlattPointPackets.S6B000068
import PlattPointPackets.S6B000069
import PlattPointPackets.S6B000070
import PlattPointPackets.S6B000071
import PlattPointPackets.S6B000072
import PlattPointPackets.S6B000073
import PlattPointPackets.S6B000074
import PlattPointPackets.S6B000075
import PlattGlobalGrid.S8B000069
namespace ChenEffective.PlattWindow.PointCovers.S8B000069
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((((ChenEffective.PlattWindow.PointPackets.S6B000062.points ++ ChenEffective.PlattWindow.PointPackets.S6B000063.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000064.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000065.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000066.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000067.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000068.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000069.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000070.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000071.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000072.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000073.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000074.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000075.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000069.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000069.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000069
