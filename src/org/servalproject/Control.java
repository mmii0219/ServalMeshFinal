package org.servalproject;

import android.annotation.TargetApi;
import android.app.Notification;
import android.app.PendingIntent;
import android.app.Service;
import android.content.Context;
import android.content.Intent;
import android.content.IntentFilter;
import android.net.ConnectivityManager;
import android.net.LocalServerSocket;
import android.net.LocalSocket;
import android.net.NetworkInfo;
import android.net.wifi.WifiConfiguration;
import android.net.wifi.WifiInfo;
import android.net.wifi.WpsInfo;
import android.net.wifi.p2p.WifiP2pConfig;
import android.net.wifi.p2p.WifiP2pDevice;
import android.net.wifi.p2p.WifiP2pDeviceList;
import android.net.wifi.p2p.WifiP2pGroup;
import android.net.wifi.p2p.WifiP2pInfo;
import android.net.wifi.p2p.WifiP2pManager;
import android.net.wifi.p2p.WifiP2pManager.ActionListener;
import android.net.wifi.ScanResult;
import android.content.BroadcastReceiver;
import android.net.wifi.WifiManager;
import android.net.wifi.p2p.WifiP2pManager.Channel;
import android.net.wifi.p2p.WifiP2pManager.PeerListListener;
import android.net.wifi.p2p.nsd.WifiP2pDnsSdServiceInfo;
import android.net.wifi.p2p.nsd.WifiP2pDnsSdServiceRequest;
import android.os.AsyncTask;
import android.os.BatteryManager;
import android.os.Binder;
import android.os.Handler;
import android.os.IBinder;
import android.os.PowerManager;
import android.text.format.Time;
import android.text.method.ScrollingMovementMethod;
import android.util.Log;
import android.view.View;
import android.widget.TextView;

import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.math.BigInteger;
import java.net.DatagramPacket;
import java.net.DatagramSocket;
import java.net.InetAddress;
import java.net.InetSocketAddress;
import java.net.NetworkInterface;
import java.net.ServerSocket;
import java.net.Socket;
import java.net.SocketException;
import java.net.SocketTimeoutException;
import java.net.UnknownHostException;
import java.nio.ByteOrder;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Timer;
import java.util.TimerTask;

import org.apache.http.conn.util.InetAddressUtils;
import org.servalproject.ServalBatPhoneApplication.State;
import org.servalproject.servald.IPeer;
import org.servalproject.servald.PeerListService;
import org.servalproject.servaldna.ServalDCommand;
import org.servalproject.servaldna.ServalDFailureException;
import org.servalproject.ui.Networks;
import org.servalproject.wifidirect.AutoWiFiDirect;

import java.io.IOException;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Date;
import java.util.Enumeration;
import java.util.Iterator;

//
import org.servalproject.wifidirect.*;

/**
 * Control service responsible for turning Serval on and off and changing the
 * Wifi radio mode.
 */
public class Control extends Service {
	private ServalBatPhoneApplication app;
	private boolean servicesRunning = false;
	private boolean serviceRunning = false;
	private SimpleWebServer webServer;
	private int peerCount = -1;
	private PowerManager.WakeLock cpuLock;
	private WifiManager.MulticastLock multicastLock = null;
	private static final String TAG = "Control";
	// Leaf0818
	private WifiP2pManager manager;
	private Channel channel;
	private final IntentFilter intentFilter = new IntentFilter();
	private BroadcastReceiver receiver = null;
	private BroadcastReceiver receiver_scan = null;
	public static boolean Isconnect = false;//判斷P2P interface有沒有被連(?)
	public String myDeviceName = null;

	private Thread t_findPeer = null;
	private Thread t_checkGO = null;
	private Thread t_wifi_connect = null;
	private Thread t_reconnection_wifiAp = null;
	private Thread t_collectIP = null;
	private Thread t_send_peer_count = null;
	private Thread t_receive_peer_count = null;
	private boolean isRunning = false;
	static public boolean Auto = false;
	private MyBinder mBinder = new MyBinder();
	// Leaf1104
	public int STATE;
	volatile private WifiManager wifi = null;
	volatile private String GOpasswd = null;
	volatile private String WiFiApName = null;
	volatile private String Cluster_Name = null;
	volatile private String Internet_Accessibility = null;

	private ConnectivityManager mConnectivityManager = null;
	/*
	 * ConnectivityManager:
	 * 可以透過ConnectivityManager這個class取得相關的資訊目前是否連上網路，
	 * 是用哪種方式連上網路，wifi or 行動網路，現在網路是不是在漫遊中...
	 */
	private NetworkInfo mNetworkInfo = null;
	private WifiP2pDnsSdServiceRequest serviceRequest = null;
	private WifiP2pDnsSdServiceInfo serviceInfo = null;
	private Map record = null;
	private Map record_re = null;
	// Leaf0616
	private int result_size = 0;
	private boolean pre_connect = false;//Wang已刪除
	private List<ScanResult> wifi_scan_results;
	private String WMNETAP = "WMNETTT"; // change to other name if you want to
										// debug without AAP case, default is
										// WMNET
	//private String WMNETAP = "CanLab";
	private String key = "lab741lab741";
	//private String key = "mikemike";
	public String s_status = "";
	private long start_time, total_time, sleep_time;
	private static int IP_port_for_IPModify = 2555;
	private static int IP_port_for_peer_counting = 2666;
	private ServerSocket ss = null;//建立ServerSocket用
	private Map<String, Integer> IPTable = new HashMap<String, Integer>();
	private Map<String, Integer> PeerTable = new HashMap<String, Integer>();
	private Socket sc; // for CollectIP_server
	private DatagramSocket receiveds; // for receive_peer_count
	private DatagramSocket receiveds_cluster;
	private int NumRound;

	// Wang
	private List<Step1Data_set> Collect_record;
	// 0 : none, 1 : go, 2 : client 3: relay

	private String GO_mac;
	private List peers = new ArrayList();
	private int power_level = 0;
	private Map<String, Map> record_set = new HashMap<String, Map>();
	private int detect_run = 0;
	private int relay_choose = 0;
	private static int IP_port_for_cluster_name = 2560;
	volatile private int ROLE = -1;
	volatile private int ChecknowRole = -1;
	volatile private int PreROLE = -1;
	volatile boolean IsNeedPeer = true;
	volatile boolean IsNeedClusterName = true;
	volatile boolean IsReceiveGoInfo = false;
	volatile private boolean IsInitial = true;
	volatile private int Time_Stamp = 0;
	private Thread initial = null;
	private Thread t_send_cluster_name = null;
	private Thread t_receive_cluster_name = null;
	private String Choose_Cluster_Name = "";
	private long initial_start_time;
	private boolean wifiScanCheck = false;
	private boolean serviceIsRegister = false;
	private Handler mServiceBroadcastingHandler;
	private boolean removeGroupCheck = false; 
	private boolean createGroupCheck = false;
	private long other_time = 0;
	private boolean addServiceCheck = false;
	private boolean checkConnect = false;//後面都註解掉了
	private boolean clientACK = false;
	private boolean relayIsconnect = false;
	private String PreClusterName = null;
	private boolean connect_check = true;
	public enum RoleFlag {
		NONE(0), GO(1), CLIENT(2), RELAY(3), WIFI_CLIENT(4);
		private int index;

		RoleFlag(int idx) {
			this.index = idx;
		}

		public int getIndex() {
			return this.index;
		}
	}

	public enum StateFlag {
		NOCONNECTION(0), GO_FORMATION(2), DETECTGAW(1), ADD_SERVICE(3), DISCOVERY_SERVICE(4), REMOVE_GROUP(
				5), WIFI_CONNECT(6), WAITING(7), RELAY(8);
		private int index;

		StateFlag(int idx) {
			this.index = idx;
		}

		public int getIndex() {
			return index;
		}
	}

	public void onNetworkStateChanged() {//好像沒用到
		if (serviceRunning) {
			Log.d("Leaf", "onNetworkStateChanged()");
			new AsyncTask<Object, Object, Object>() {

				@Override
				protected Object doInBackground(Object... params) {
					modeChanged();
					return null;
				}
			}.execute();
		}
	}

	private synchronized void startServices() {//於modeChanged內呼叫
		if (servicesRunning)//初始值為false; 於startServices設定為true; 於stopServices設定為false
			return;
		Log.d("wang", "Starting services");//Miga20180115 ori:Log.d(TAG, "Starting services")
		servicesRunning = true;
		cpuLock.acquire();
		multicastLock.acquire();
		try {
			app.server.isRunning();
		} catch (ServalDFailureException e) {
			app.displayToastMessage(e.getMessage());
			Log.e(TAG, e.getMessage(), e);
		}
		peerCount = 0;
		updateNotification();
		try {
			ServalDCommand.configActions(ServalDCommand.ConfigAction.del, "interfaces.0.exclude",
					ServalDCommand.ConfigAction.sync);
		} catch (ServalDFailureException e) {
			Log.e(TAG, e.getMessage(), e);
		}
		try {
			if (webServer == null)
				webServer = new SimpleWebServer(8080);
		} catch (IOException e) {
			Log.e(TAG, e.getMessage(), e);
		}
	}

	private synchronized void stopServices() {//於modeChanged內呼叫
		if (!servicesRunning)//若是沒有進入startServices,則此變數就會一直為false
			return;

		Log.d("Wang", "Stopping services");//Miga20180115 ori:Log.d(TAG, "Stopping services")
		servicesRunning = false;
		multicastLock.release();
		try {
			ServalDCommand.configActions(ServalDCommand.ConfigAction.set, "interfaces.0.exclude", "on",
					ServalDCommand.ConfigAction.sync);
		} catch (ServalDFailureException e) {
			Log.e(TAG, e.getMessage(), e);
		}
		peerCount = -1;
		if (webServer != null) {
			webServer.interrupt();
			webServer = null;
		}

		this.stopForeground(true);
		cpuLock.release();
	}

	private synchronized void modeChanged() {//於callAsynchronousTask內呼叫,每兩秒執行一次modeChanged
		/*Wang
		checkRole();*/
		boolean wifiOn = app.nm.isUsableNetworkConnected();

		Log.d(TAG, "modeChanged(" + wifiOn + ")");

		// if the software is disabled, or the radio has cycled to sleeping,
		// make sure everything is turned off.
		if (!serviceRunning)
			wifiOn = false;

		if (multicastLock == null) {
			WifiManager wm = (WifiManager) getSystemService(Context.WIFI_SERVICE);
			multicastLock = wm.createMulticastLock("org.servalproject");
		}

		if (wifiOn == true || Isconnect == true) {//在Initial的ROLE=NONE時,manager.createGroup會將Isconnect設為true; thread.sleep兩秒後執行manager.removeGroup, 將Isconnect設為false
			Log.d("Leaf0709", "Start Sevice");
			startServices();
		} else {
			stopServices();
		}
	}

	// Wang new add to check exception detail
	public static String getStackTrace(final Throwable throwable) {
	     final StringWriter sw = new StringWriter();
	     final PrintWriter pw = new PrintWriter(sw, true);
	     throwable.printStackTrace(pw);
	     return sw.getBuffer().toString();
	}
	
	public void callAsynchronousTask() {//用來每兩秒執行一次modeChanged()
    final Handler handler = new Handler();
    Timer timer = new Timer();
    TimerTask doAsynchronousTask = new TimerTask() {       
        @Override
        public void run() {
            handler.post(new Runnable() {
                public void run() {       
                    try {
                    	/*if(app.getState() == State.Off) {	
                    		modeChanged();
                    		app.setState(State.On);
                    		Log.d("Wang", "state is change");
                    	}else {*/
                    		modeChanged();
                    		//Log.d("Wang", "mode change" + app.getState());
                    		//Log.d("Wang", "mode change" + " " + ServalDCommand.serverStatus());
                    		String server_status = ServalDCommand.serverStatus().status;
                    		if(server_status.equals("stopped")) {
                    			/*String server_stop = null;
                    			server_stop  =ServalDCommand. serverStop().status;
                    			while(server_stop == null){};*/
                    			try{
                    				ServalDCommand.serverStart();
                    			}catch(ServalDFailureException e){
                    				Log.d("Wang", getStackTrace(e));
                    			}
                    		}
                    	//}
                        // PerformBackgroundTask this class is the class that extends AsynchTask 
                    } catch (Exception e) {
                        // TODO Auto-generated catch block
                    }
                }
            });
        }
    };
    timer.schedule(doAsynchronousTask, 0, 2000); //execute doAsynchronousTask in every 2000 ms
}


	private void updateNotification() {
		if (!servicesRunning)
			return;

		Notification notification = new Notification(R.drawable.ic_serval_logo, getString(R.string.app_name),
				System.currentTimeMillis());

		Intent intent = new Intent(app, Main.class);
		intent.setFlags(Intent.FLAG_ACTIVITY_CLEAR_TOP);

		notification.setLatestEventInfo(Control.this, getString(R.string.app_name),
				app.getResources().getQuantityString(R.plurals.peers_label, peerCount, peerCount),
				PendingIntent.getActivity(app, 0, intent, PendingIntent.FLAG_UPDATE_CURRENT));

		notification.flags = Notification.FLAG_ONGOING_EVENT;
		this.startForeground(-1, notification);
	}

	private synchronized void startService() {
		Log.e("Leaf", "modeChanged");
		app.controlService = this;
		app.setState(State.Starting);
		try {
			this.modeChanged();
			app.setState(State.On);
		} catch (Exception e) {
			app.setState(State.Off);
			Log.e("BatPhone", e.getMessage(), e);
			app.displayToastMessage(e.getMessage());
		}
	}

	private synchronized void stopService() {
		Log.e("Leaf", "Control_stopService()");
		app.setState(State.Stopping);
		app.nm.onStopService();
		stopServices();
		app.setState(State.Off);
		app.controlService = null;
	}

	public void updatePeerCount(int peerCount) {
		if (this.peerCount == peerCount)
			return;
		this.peerCount = peerCount;
		updateNotification();
	}
//170915 確認剩下的function是否有使用到?
	class Task extends AsyncTask<State, Object, Object> {
		@Override
		protected Object doInBackground(State... params) {
			//Log.d("Wang", "mode change");
			if (app.getState() == params[0])
				return null;

			if (params[0] == State.Off) {
				stopService();
			} else {
				startService();
			}
			return null;
		}
	}

	private int Newcompare(String a, String b) {//比較a和b的字典序,長度
		int alength = a.length();
		int blength = b.length();
		char[] A = a.toCharArray();
		char[] B = b.toCharArray();
		int i, j;
		int result = 0;
		for (i = 0, j = 0; i < alength && j < blength; i++, j++) {
			if (A[i] != B[j]) {
				return A[i] - B[j];
			}
		}
		if (alength > blength) {
			return 1;
		} else if (alength < blength) {
			return -1;
		}
		return result;
	}

	public class Step1Data_set {
		private String SSID;
		private String key;
		private String Name;
		private String In_ac;
		private String PEER;
		private String MAC;
		private String POWER;
		private String GO;

		public Step1Data_set(String SSID, String key, String Name, String In_ac, String PEER, String MAC,
				String POWER, String GO) {
			this.SSID = SSID;
			this.key = key;
			this.Name = Name;
			this.In_ac = In_ac;
			this.PEER = PEER;
			this.MAC = MAC;
			this.POWER = POWER;
			this.GO = GO;
		}

		String getSSID() {
			return this.SSID;
		}

		String getkey() {
			return this.key;
		}

		String getName() {
			return this.Name;
		}

		String getIn_ac() {
			return this.In_ac;
		}

		String getPEER() {
			return this.PEER;
		}

		String getMAC() {
			return this.MAC;
		}

		String getPOWER() {
			return this.POWER;
		}
		
		String getGO() {
			return this.GO;
		}

		public boolean equals(Object object) {
			Step1Data_set other = (Step1Data_set) object;
			if (this.SSID.equals(other.SSID) == true)
				return true;

			return false;
		}

		public String toString() {
			return this.SSID + " " + this.Name + " " + this.In_ac + " " + this.PEER + " " + this.MAC + " " + this.POWER;
		}

		public int compareTo(Step1Data_set data) {//1. power 2. SSID , In_ac在良辰的裡面應該都是一致的
			String SSID = data.getSSID();
			String In_ac = data.getIn_ac();
			String POWER = data.getPOWER();

			if (this.In_ac.compareTo(In_ac) < 0) {
				return 1;//data大(o2)
			} else if (this.In_ac.compareTo(In_ac) > 0) {
				return -1;
			}

			
			if (this.POWER.equals("100")) {
				return -1;//o1較大
			} else if(POWER.equals("100")) {
				return 1;//o2較大
			}else if (this.POWER.compareTo(POWER) < 0) {
				return 1;
			} else if (this.POWER.compareTo(POWER) > 0) {
				return -1;
			}

			if (this.SSID.compareTo(SSID) < 0) {
				return 1;
			} else if (this.SSID.compareTo(SSID) > 0) {
				return -1;
			}

			return 0;
		}
	}

	public class Step2Data_set_Comparator implements Comparator {

		public int compare(Object obj1, Object obj2) {
			Step1Data_set data1 = (Step1Data_set) obj1;
			Step1Data_set data2 = (Step1Data_set) obj2;

			if (data1.getIn_ac().compareTo(data2.getIn_ac()) < 0) {
				return 1;
			} else if (data1.getIn_ac().compareTo(data2.getIn_ac()) > 0) {
				return -1;
			}
			

			if (data1.getPOWER().equals("100")) {
				return 1;
			} else if(data2.getPOWER().equals("100")) {
				return -1;
			}else if (data1.getPOWER().compareTo(data2.getPOWER()) < 0) {
				return -1;
			} else if (data1.getPOWER().compareTo(data2.getPOWER()) > 0) {
				return 1;
			}

			if (data1.getPEER().compareTo(data2.getPEER()) < 0) {
				return 1;
			} else if (data1.getPEER().compareTo(data2.getPEER()) > 0) {
				return -1;
			}

			if (data1.getSSID().compareTo(data2.getSSID()) < 0) {
				return 1;
			} else if (data1.getSSID().compareTo(data2.getSSID()) > 0) {
				return -1;
			}

			return 0;

		}
	}

	public static String getP2PIpAddress() {
		try {
			List<NetworkInterface> interfaces = Collections.list(NetworkInterface.getNetworkInterfaces());
			for (NetworkInterface intf : interfaces) {
				if (!intf.getName().contains("p2p"))
					continue;//沒有包含p2p則continue

				List<InetAddress> addrs = Collections.list(intf.getInetAddresses());

				for (InetAddress addr : addrs) {
					// Log.v("Wang", "inside");

					if (!addr.isLoopbackAddress()) {
						// Log.v("Wang", "isnt loopback");
						String sAddr = addr.getHostAddress().toUpperCase();
						Log.v("Wang", "ip=" + sAddr);

						boolean isIPv4 = InetAddressUtils.isIPv4Address(sAddr);

						if (isIPv4) {
							if (sAddr.contains("192.168.49.")) {
								Log.v("Wang", "ip = " + sAddr);
								return sAddr;
							}//End contains 192.168.49.1
						}//End isIPv4
					}//End !addr.isLoopbackAddress
				}//End for addr : addrs
			}//End for intf : interfaces
		} catch (Exception ex) {
			Log.v("Wang", "error in parsing");
		} // for now eat exceptions
		Log.v("Wang", "returning empty ip address");
		return "";
	}

	public class Initial extends Thread {

		public void run() {
			//newWang
			initial_start_time = Calendar.getInstance().getTimeInMillis();
			// 可能裝置先用手動連線 check role
			// 因為是在開啟 enable 之前就先用手動連線 所以 AutoWiFiDirect 監聽者 無法收到 p2p 的變化 所以
			// Isconnected無法使用
			// 因此需要呼叫 p2pmanager 來判斷
			manager.requestGroupInfo(channel, new WifiP2pManager.GroupInfoListener() {//manage: Wifi Direct Manager 
				@Override
				public void onGroupInfoAvailable(WifiP2pGroup group) {
					//onGroupInfoAvailable: The requested p2p group info is available
					if (group != null) {
						Log.d("Wang", "Group is not null");
						if (group.isGroupOwner() == true) {
							Log.d("Wang", "I am GO");
							ROLE = RoleFlag.GO.getIndex();
							GOpasswd = group.getPassphrase();
							//getNetworkName: Get the network name (SSID) of the group. 
							//Legacy Wi-Fi clients will discover the p2p group using the network name.
							WiFiApName = group.getNetworkName();//SSID
							Cluster_Name = WiFiApName;//SSID
							GO_mac = group.getOwner().deviceAddress.toString();
							Isconnect = true;//Isconnect是p2p的connect，不是Wifi的
						} else {//不是GO
							ROLE = RoleFlag.NONE.getIndex();
						}
					}
				}
			});
			
			try {
				Thread.sleep(500);
			} catch (InterruptedException e1) {
				// TODO Auto-generated catch block
				e1.printStackTrace();
			}
			Log.d("Wang", "Cluster_Name " + Cluster_Name);
			//mConnectivityManager:管理連線狀態的manager
			if (mConnectivityManager != null) {
				mNetworkInfo = mConnectivityManager.getNetworkInfo(ConnectivityManager.TYPE_WIFI);
			}

			if (mNetworkInfo.isConnected() == true && mNetworkInfo != null) {//wifi interface已連上
				if (ROLE == RoleFlag.GO.getIndex()) {
					ROLE = RoleFlag.CLIENT.getIndex();//覺的可能是relay candidate? 或有[可能是connected GO的第二種情況(word)--> Y]
				} else {//ROLE!=GO
					manager.requestConnectionInfo(channel, new WifiP2pManager.ConnectionInfoListener() {//manager.requestConnectionInfo: Request device connection Info
						public void onConnectionInfoAvailable(WifiP2pInfo info) {//onConnectionInfoAvailable: The requested connection info is available
							if (info.groupFormed == true) {// groupFormed: Indicates if a p2p group has been successfully formed
								ROLE = RoleFlag.RELAY.getIndex();//wifi interface已連上,且也有p2p group
								Isconnect = true;
							} else {
								ROLE = RoleFlag.WIFI_CLIENT.getIndex();//只有wifi interface連上而已, p2p group沒有(請看ppt 3ec4的情況,事先建立ROLE情境1)
							}
						}
					});
				}
			}
			try {
				Thread.sleep(1000);
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
			if (ROLE == RoleFlag.WIFI_CLIENT.getIndex()) {//以p2p interface建立GO,這樣WIFI_CLIENT就可以變成Relay Candidate
				manager.createGroup(channel, new WifiP2pManager.ActionListener() {//manager:Wifi Direct's Manager
					@Override
					public void onSuccess() {
						Log.d("Wang", "wifi client createGroup Success");
						Isconnect = true;
					}
					@Override
					public void onFailure(int error) {
						Log.d("Wang", "wifi client createGroup onFailure");
					}
				});
				try {
					Thread.sleep(1000);
				} catch (InterruptedException e) {
					e.printStackTrace();
				}
				manager.requestGroupInfo(channel, new WifiP2pManager.GroupInfoListener() {
					@Override
					public void onGroupInfoAvailable(WifiP2pGroup group) {
						if (group != null) {
							Log.d("Wang", "group is not null");
							if (group.isGroupOwner() == true) {//WIFI CLIENT以p2p 建立一個group,因此也是GO
								Log.d("Wang", "wifi client request the go info success ");
								GOpasswd = group.getPassphrase();
								WiFiApName = group.getNetworkName();
								Cluster_Name = WiFiApName;
								GO_mac = group.getOwner().deviceAddress.toString();
							}
						}
					}
				});
				ROLE = RoleFlag.CLIENT.getIndex();
				try {
					Thread.sleep(500);
				} catch (InterruptedException e) {
					e.printStackTrace();
				}
			}//End WIFI_CLIENT
			if(ROLE == RoleFlag.CLIENT.getIndex()){
				manager.requestGroupInfo(channel, new WifiP2pManager.GroupInfoListener() {
					@Override
					public void onGroupInfoAvailable(WifiP2pGroup group) {
						if (group != null) {
							if(!group.getClientList().isEmpty()){//有client
								ROLE = RoleFlag.GO.getIndex();//在line675從GO->CLIENT.實質上他也是個GO,因此列出有連上他的client之後,ROLE就轉回GO
								Log.d("Wang", group.getClientList().toString());
							}
						} 
					}
				});
			}//End CLIENT
			if (ROLE != RoleFlag.NONE.getIndex()) {//不為NONE
				try {
					Thread.sleep(3000);
				} catch (InterruptedException e) {
					e.printStackTrace();
				}
				int tryNum = 0;
				Initial_IP_table();//傳送該裝置的wifi ip address並傳送給go檢查IP Table內是否有重複的ip, 若沒有的話則加入到IP Table內並將ip設為static;若有的話則重新產生一組新的ip
				
				// 為了更新clustername 預留時間
				try {
					Thread.sleep(5000);
				} catch (InterruptedException e) {
					e.printStackTrace();
				}

				
				 tryNum = 0;
				while (tryNum < 15) {
					peerCount = count_peer();//計算PeerTable內有幾個不同的SSID
					tryNum++;
					// Log.d("Wang", "Peer: " + peerCount);
					try {
						Thread.sleep(100);
					} catch (InterruptedException e1) {
						// TODO Auto-generated catch block
						e1.printStackTrace();
					}
				}
			}//END !=NONE


			if (ROLE == RoleFlag.WIFI_CLIENT.getIndex()) {//這裡跟line 694重複?
				manager.createGroup(channel, new WifiP2pManager.ActionListener() {
					@Override
					public void onSuccess() {
						Log.d("Wang", "wifi client createGroup Success");
						Isconnect = true;
					}

					@Override
					public void onFailure(int error) {
						Log.d("Wang", "wifi client createGroup onFailure");
					}
				});
				ROLE = RoleFlag.CLIENT.getIndex();
			}//End WIFI_CLIENT
			try {
				Thread.sleep(1000);
			} catch (InterruptedException e) {
				e.printStackTrace();
			}

			Log.d("Wang", "ROLE: " + ROLE);

			if (ROLE == RoleFlag.NONE.getIndex()) {//進行初始化,將WiFiApName,Cluster_Name等等那些東西先藉由建立p2p group後指定好.指定好後在將p2p group移除。
				manager.createGroup(channel, new WifiP2pManager.ActionListener() {
					@Override
					public void onSuccess() {
						Log.d("Wang", "initial createGroup Success");
						Isconnect = true;
					}
					@Override
					public void onFailure(int error) {
						Log.d("wang", "initial createGroup onFailure");
					}
				});
				try {
					Thread.sleep(1000);
				} catch (InterruptedException e) {
					e.printStackTrace();
				}

				manager.requestGroupInfo(channel, new WifiP2pManager.GroupInfoListener() {
					@Override
					public void onGroupInfoAvailable(WifiP2pGroup group) {
						if (group != null) {
							GOpasswd = group.getPassphrase();
							WiFiApName = group.getNetworkName();
							Cluster_Name = WiFiApName;
							// Wang
							GO_mac = group.getOwner().deviceAddress.toString();
							//while(WiFiApName == null){};
						}
					}
				});
				
				try {
					Thread.sleep(1000);
				} catch (InterruptedException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				manager.removeGroup(channel, new WifiP2pManager.ActionListener() {
					@Override
					public void onSuccess() {
						Log.d("Wang", "initial remove group success");
						Isconnect = false;
					}
					@Override
					public void onFailure(int reason) {
						Log.d("Wang", "initial remove group failure");
					}
				});
			}//End NONE
			Log.d("Wang", "peerCount : " + peerCount);
			updatePeerCount(peerCount);
			IsInitial = false;
			s_status = "State: Initial Complete : time : " +( (Calendar.getInstance().getTimeInMillis() - initial_start_time)/1000 + " SSID : " + WiFiApName + " Cluster_Name : " + Cluster_Name)+
					" ROLE : " + ROLE + " IPTABLE " + IPTable;
			//s_status = "State: Initial Complete : " + " SSID : " + WiFiApName + " Cluster_Name : " + Cluster_Name ;
			
		}
	}
  
	//在Initial時會執行
	public void Initial_IP_table() {//client傳送自己的wifi ip address給go檢查, 檢查看看是否有重複了, 若沒有重覆則將ip設為static的
		int Num = 0;
		String message = wifiIpAddress();//取得wifi ip address
		if(message == null)//wifi interface沒有連
			return;
		if (message != null) {//wifi interface有
			IPTable = new HashMap<String, Integer>();
			IPTable.put(message, 0);
			Log.d("Wang", "State: set IPTable: " + Integer.valueOf(message.substring(message.lastIndexOf(".") + 1)));
			while (Num < 5) {
				try {//這邊有點像是client要傳送給server(GO) data
					/* 
					 * To send data through the socket to the server, 
					 * the EchoClient example needs to write to the PrintWriter. 
					 * To get the server's response, 
					 * EchoClient reads from the BufferedReader object stdIn,
					 */
					// socket(hostName, port) ,hostName 表示目的端 IP
					Socket Client_socket = new Socket("192.168.49.1", IP_port_for_IPModify);//The Socket constructor used here requires the name of the computer and the port number to which you want to connect. 
					PrintWriter out = new PrintWriter(Client_socket.getOutputStream());// gets the socket's output stream and opens a PrintWriter on it. 
					Log.d("Wang", "Send message: " + message);
					out.println(message);//傳送message給GO. sends it to the server by writing it to the PrintWriter connected to the socket 
					out.flush();
					BufferedReader in = new BufferedReader(new InputStreamReader(Client_socket.getInputStream()));// gets the socket's input stream and opens a BufferedReader on it
					message = in.readLine();//讀取從server (GO)回傳回來的message 於CollectIP_server()
					Log.d("Wang", "Receive message: " + message);
					String[] s = message.split(":");//回傳的message可能為 YES:192.168.49.x or NO:X
					Log.d("Wang", "Split result: " + s[0] + " " + s[1]);
					// if (Newcompare(s[0], "YES") == 0) {
					// wifi direct 是用 dhcp 分配 ip 對於 dhcp 而言 ip 可能過期而重新分配 這樣
					// 在建立 routing table 會有麻煩 因此使用 static
					boolean result = setIpWithTfiStaticIp(s[1]);
					String newWiFiIP = wifiIpAddress();//Add by Miga , 取得新的wifi ip address
					Log.d("Wang", "Modify the static IP address: " +newWiFiIP+","+ result);
					// }
					Num = 5;
					in.close();
					out.close();
					Client_socket.close();
				} catch (Exception e) {
					e.printStackTrace();
				}
				Num++;
			}
		}
	}

	
	public class WiFi_Connect extends Thread {
		int TryNum;
		//當收到Service Response時，做判斷以及連線
		public void run() {
			STATE = StateFlag.WAITING.getIndex();//7
			try {
				// collect data
				
				if (ROLE != -1) {
					PreROLE = ROLE;
				}
				clientACK = false;
				int collect_num = 10;
				String thisTimeMAC = record.get("MAC").toString();//record是對方的服務內容（在discovery Service時指定了record=re_record）
				while (collect_num > 0) {
					record_set.put(record.get("SSID").toString(), record);//將蒐集到的其他裝置的服務根據SSID存放個別的服務
					Thread.sleep(100);
					collect_num--;
				}
				sleep_time = sleep_time + 1000;
				String SSID = null;
				String key=null;
				String Name=null;
				String In_ac=null;
				String PEER=null;
				String MAC=null;
				String POWER=null;
				String GO;
				if (record_set.size() == 0) {
					Log.d("Wang", "Collect data and record size = 0");
					STATE = StateFlag.ADD_SERVICE.getIndex();//3
					return;
				}
				//Log.d("Wang", "Collect data and record size : " + record_set.size());
				//s_status = "State: Collect data";
				//Stringrecord_set_key
				Collect_record.clear();
				for (Object set_key : record_set.keySet()) {//keySet(): 獲取map集合中的所有鍵的set集合
					//set_key應該是一堆SSID的集合
					record = record_set.get(set_key);//根據set_key(也就是SSID)來取得對應的value, 這邊value就是map型態的record
					SSID = record.get("SSID").toString();//WiFiApName
					key = record.get("PWD").toString();
					Name = record.get("Name").toString();//Cluster_Name
					In_ac = record.get("In_ac").toString();
					PEER = record.get("PEER").toString();
					MAC = record.get("MAC").toString();
					POWER = record.get("POWER").toString();
					GO = record.get("GO").toString();
					// Log.d("Wang", "Insert data");
					//experiment to use
					if(Name.equals("AutoFalse")) {
						continue;
					}
					if(!Name.equals(Cluster_Name)) {//Name!=Cluster_Name則進入,應該是蒐集到的device的Cluster_Name和自己的Cluster_Name不相同
						Step1Data_set data = new Step1Data_set(SSID, key, Name, In_ac, PEER, MAC, POWER, GO);//這邊應該是用來Cluster Initialization用,投影片p25
						if (!Collect_record.contains(data)) {//判斷Collect_record內是否已經有data, Collect_record是專門儲存別的device的data,不過下面幾行的code也是有儲存自己device的info
							Collect_record.add(data);//沒有的話則將data加入到Collect_record
						}
					}
				}//End for
				String slef_GO = "FALSE";
				if(ROLE==RoleFlag.GO.getIndex()) {
					slef_GO= "TRUE";
				}
				//自己的資訊
				Step1Data_set self = new Step1Data_set(WiFiApName, GOpasswd, Cluster_Name, Internet_Accessibility,
						String.valueOf(peerCount), GO_mac, String.valueOf(power_level), slef_GO);

				if (!Collect_record.contains(self)) {
					Collect_record.add(self);//存自己的data到Collect_record
				}
				//Log.d("Wang", "record size " + Collect_record.size());
				//s_status = "State: record size " + Collect_record.size();
				Collections.sort(Collect_record, new Comparator<Step1Data_set>() {//根據Step1Data_set的compareTo內的方法來進行排序,這個排序是良辰的policy1: battery power, SSID
					public int compare(Step1Data_set o1, Step1Data_set o2) {//Collect_record內有自己這個device的data也有他收集到其他device的data, 這些去進行policy1的排序後選出誰是GO
						return o1.compareTo(o2);
					}
				});
				int obj_num = 0;
				String Collect_contain = "";
				Step1Data_set tmp;
				for (int i = 0; i < Collect_record.size(); i++) {
					tmp = (Step1Data_set) Collect_record.get(i);
					Collect_contain = Collect_contain + obj_num + " : " + tmp.toString() + " ";//目的應該只是要print出有收集到哪些data
					obj_num++;
				}
				Log.d("Wang", "Collect records contain " + Collect_contain);
				
				//test
				//這邊抓get(0)的用意應該是要抓出目前排序第一個device,之後是要來當作GO用的(可能是自己or其他device)
				SSID = Collect_record.get(0).getSSID();
				key = Collect_record.get(0).getkey();
				Name = Collect_record.get(0).getName();
				In_ac = Collect_record.get(0).getIn_ac();
				PEER = Collect_record.get(0).getPEER();
				MAC = Collect_record.get(0).getMAC();
				// peerCount = count_peer();

				// check role
				if (mConnectivityManager != null) {
					mNetworkInfo = mConnectivityManager.getNetworkInfo(ConnectivityManager.TYPE_WIFI);
				}
				if (mNetworkInfo.isConnected() == true && mConnectivityManager != null) {//判斷wifi interface有沒有連上
					if (Isconnect == true) {//Isconnect是p2p的connect，只要有成功建立p2p group則Isconnect=true
						String p2p_Ip = ""; 
						p2p_Ip = getP2PIpAddress();//取得p2p interface's  ip address
						if (p2p_Ip.equals("192.168.49.1") == true ||p2p_Ip == null ) {
							ROLE = RoleFlag.CLIENT.getIndex();//應該是Connect_GO的第二種圖的情況,因為他的wifi也去連上了另個device並成為他的CLIENT//Miga 20180122 或是原本從GO->Client 但是因為他還沒解除p2p group且Isconnect也還沒變為f//20180125 或是手動建立的情況,先以wifi連上go,接著p2p事由code自動幫他建立的
							Log.d("Wang", "p2p_Ip:"+p2p_Ip+"ROLE:"+ROLE);//Add by Miga 20180125
						} else {
							ROLE = RoleFlag.RELAY.getIndex();//WIFI interface(isConnected()==true)跟p2p interface(Isconnect==true)都有連上
						}
					}
				} else {//wifi interface沒連上
					if (Isconnect == true) {//p2p interface有連上
						//ROLE = RoleFlag.GO.getIndex();//Miga20180117 why良辰註解?????
						Cluster_Name = WiFiApName;//只有p2p interface有連上
					} else {
						ROLE = RoleFlag.NONE.getIndex();//Wifi interface和p2p interface都是false
					}
				}
				if(ROLE == RoleFlag.CLIENT.getIndex() ) {
					if(clientACK == true) {//Receive_Cluster_Name時會改變
						ROLE = RoleFlag.GO.getIndex();//可能是Connected GO的第二張圖中間device
						Log.d("Wang", "clientACK:"+clientACK+"ROLE:"+ROLE);//Add by Miga 20180125
					}
				}
				// Initial_IP_table();
				if(ROLE !=  RoleFlag.NONE.getIndex()){
					TryNum = 0;
					while (peerCount <= 0 && TryNum < 5) {
						//Log.d("Wang", "State: acquiring the newest information at first phase");
						peerCount = count_peer();
						//peerCount = ServalDCommand.peerCount();
						Thread.sleep(1000);
						sleep_time = sleep_time + 1000;
						TryNum++;
					}
					updatePeerCount(peerCount);
				}

				// GO檢查自己是否被其他裝置連
				if ( ROLE == RoleFlag.GO.getIndex()) {
					if(peerCount > 0) {//Miga20180117 peerCount應該是計算同個cluster內裡面有幾個device,若是>0的話表示GO有被其他裝置連(因為同cluster內數量>0)
						detect_run = 0;
						STATE = StateFlag.ADD_SERVICE.getIndex();
						return;
					}else if(detect_run < 5){
						detect_run++;
						STATE = StateFlag.ADD_SERVICE.getIndex();
						return;
					}
				}
				//利用line1080抓get(0)來檢查
				if (SSID.equals(WiFiApName) ) {//會相等表示line1080抓到的是自己的data(自己將來應該是這群device的GO),因此檢查有沒有被其他裝置連並且檢查是否孤立
					if( ROLE == RoleFlag.GO.getIndex()){
						// 被孤立的GO(?) //Miga20180117 會執行到這邊的原因是因為GO被孤立了,因為他的peerCount不大於0,表示他的cluster內只有自己一個人
						if(Collect_record.get(1) != null) {//因為自己是GO,但是peerCount又沒有>0,表示說應該是被孤立了,因此將SSID改設為排序第二的device,之後可能會連到該device
							SSID = Collect_record.get(1).getSSID();//因此這個被孤立的GO//Miga20180117 peerCount應該是計算同個cluster內裡面有幾個device,若是>0的話表示GO有被其他裝置連(因為同cluster內數量>0)
							key = Collect_record.get(1).getkey();
							Name = Collect_record.get(1).getName();
							In_ac = Collect_record.get(1).getIn_ac();
							PEER = Collect_record.get(1).getPEER();
							MAC = Collect_record.get(1).getMAC();
						}else {//完全被孤立,附近都沒有裝置可以連,因此回到ADD_SERVICE繼續搜尋
							detect_run = 0;
							STATE = StateFlag.ADD_SERVICE.getIndex();
							return;
						}
					}else if (ROLE == RoleFlag.NONE.getIndex()) {//若裝置一開始的ROLE==NONE時, 且收集到其他device的info,但自身裝置以policy1排序後是第一(表示將來會是GO),則會進入
						ROLE = RoleFlag.GO.getIndex();
						STATE = StateFlag.GO_FORMATION.getIndex();
						return;		
					} 
				}
				// Wang
				// become client

				//用WIFI_INTERFACE去聯別人
				STATE = StateFlag.WIFI_CONNECT.getIndex();//WIFI_CONNECT只有在這邊有用到而已,其他地方都沒有
				s_status = "State: choosing peer";
				Log.d("Leaf0419", "State: choosing peer");

				try {
					if (ROLE == RoleFlag.NONE.getIndex() || ROLE == RoleFlag.GO.getIndex()) {//device從ROLE=NONE變為CLIENT;而GO的話表示這個GO是被孤立的,但是有搜尋到其他裝置,因此這邊就是改成連上到該裝置,當作該裝置的clinet?
						//Miga 20180118既然是被孤立的GO,但已經有其他device可以連上,是不是應該在GO連上該device之前,先把GO的p2p interface移除,並把isConnect設為false呢?下面的程式碼好像沒有看到這一段!!!!!!!!!!!!!
						if (mConnectivityManager != null) {
							mNetworkInfo = mConnectivityManager.getNetworkInfo(ConnectivityManager.TYPE_WIFI);
							if (mNetworkInfo != null) {
								if (mNetworkInfo.isConnected() == true) {//Wifi interface有連上
									wifi.disconnect();//斷掉wifi interface的連線,
									Thread.sleep(1000);
									sleep_time = sleep_time + 1000;
								}
							}
						}
						List<WifiConfiguration> list = wifi.getConfiguredNetworks();
						for (WifiConfiguration i : list) {
							wifi.removeNetwork(i.networkId);//移除所有之前wifi連線網路的設定
							wifi.saveConfiguration();//除存設定
						}
						// Try to connect Ap(連上排序第一個or第二個的裝置)
						WifiConfiguration wc = new WifiConfiguration();
						s_status = "State: choosing peer done, try to associate with" + ": SSID name: " + SSID + " , passwd: " + key;
						Log.d("Leaf0419", "State: choosing peer done, try to associate with" + ": SSID name: " + SSID + " , passwd: " + key);
						wc.SSID = "\"" + SSID + "\"";
						wc.preSharedKey = "\"" + key + "\"";
						wc.hiddenSSID = true;
						wc.status = WifiConfiguration.Status.ENABLED;
						wc.allowedGroupCiphers.set(WifiConfiguration.GroupCipher.TKIP);
						wc.allowedGroupCiphers.set(WifiConfiguration.GroupCipher.CCMP);
						wc.allowedKeyManagement.set(WifiConfiguration.KeyMgmt.WPA_PSK);
						wc.allowedPairwiseCiphers.set(WifiConfiguration.PairwiseCipher.TKIP);
						wc.allowedPairwiseCiphers.set(WifiConfiguration.PairwiseCipher.CCMP);
						wc.allowedProtocols.set(WifiConfiguration.Protocol.RSN);
						TryNum = 15;
						wifiScanCheck = false;
						//Log.d("Leaf0419", "State: Scan before");
						wifi.startScan();//startScan完畢後，wifi會呼叫SCAN_RESULTS_AVAILABLE_ACTION
						long wifiscan_time_start = Calendar.getInstance().getTimeInMillis() ;
						while(wifiScanCheck == false) {//在onCreate時有註冊一個廣播器,專門來徵測wifi scan的結果,wifi.startscan完畢後,wifiScabCheck應該會變為true
						};

						//Log.d("Leaf0419", "State: Scan After");
						sleep_time = sleep_time + Calendar.getInstance().getTimeInMillis() - wifiscan_time_start;
						wifiScanCheck = false;
						boolean findIsGoExist = false;
					
						for(int i = 0; i < wifi_scan_results.size(); i++) {//檢查接下來要連上的GO還在不在,wifi_scan_results:會列出掃描到的所有AP
							ScanResult sr = wifi_scan_results.get(i);
							if(sr.SSID.equals(SSID)) {//去比對每一個掃描到的AP,看是不是我們要連上的GO,若是則將findIsGoExist設為true並跳出for迴圈
								findIsGoExist = true;
								break;
							}
						}
						Log.d("Wang", "findIsGoExist : " +findIsGoExist);
						if(findIsGoExist == false) {//若我們要連的GO不見的話,則回到ADD_SERVICE,重新再收集資料一次
							STATE = StateFlag.ADD_SERVICE.getIndex();
							return;
						}
						//使用wifi interface連線,連上GO
						int res = wifi.addNetwork(wc);
						boolean temp = wifi.enableNetwork(res, true);

						if (mConnectivityManager != null) {
							mNetworkInfo = mConnectivityManager.getNetworkInfo(ConnectivityManager.TYPE_WIFI);
							if (mNetworkInfo != null) {
								while (!mNetworkInfo.isConnected() && TryNum >= 0) {//wifi interface沒成功連上,開始不斷嘗試連接
									temp = wifi.enableNetwork(res, true);
									Thread.sleep(1000);
									sleep_time = sleep_time + 1000;
									TryNum--;

									s_status = "State: associating GO, enable true:?" + temp + " remainder #attempt:"
											+ TryNum;
									Log.d("Leaf0419", "State: associating GO, enable true:?" + temp
											+ " remainder #attempt:" + TryNum);
									mNetworkInfo = mConnectivityManager.getNetworkInfo(ConnectivityManager.TYPE_WIFI);
								}//End While

								if (mNetworkInfo.isConnected() == true) {//wifi interface已經連上,可以開始連p2p
									// renew service record information
									Cluster_Name = Name;//將自己的Cluster_Name更新為新的GO的Cluster_Name //Miga 20180118 將自己的clusterName更新了
									Internet_Accessibility = In_ac;
									removeGroupCheck = true;
									//check whether change IP
									String message = wifiIpAddress();//取得wifi IP address
                                    IPTable = new HashMap<String, Integer>();
                                    IPTable.put(message, 0);
                                    Log.d("Leaf0419", "State: set IPTable: " + Integer.valueOf(message.substring(message.lastIndexOf(".") + 1)));
                                    TryNum = 0;
                                    while (TryNum < 5) {
                                        try {
                                            Socket Client_socket = new Socket("192.168.49.1", IP_port_for_IPModify);
                                            PrintWriter out = new PrintWriter(Client_socket.getOutputStream());
                                            Log.d("Leaf0419", "Send message: " + message);//傳送device的ip address給GO
                                            out.println(message);
                                            out.flush();
                                            BufferedReader in = new BufferedReader(new InputStreamReader(Client_socket.getInputStream()));
                                            message = in.readLine();
                                            Log.d("Leaf0419", "Receive message: " + message);//從GO那裡接收到的結果
                                            String[] s = message.split(":");
                                            Log.d("Leaf0419", "Split result: " + s[0] + " " + s[1]);
                                            if (Newcompare(s[0], "YES") == 0) {//ip address重複了,因此需要設定新的ip address
                                                boolean result = setIpWithTfiStaticIp(s[1]);
                                                Log.d("Leaf0419", "Modify the static IP address: " + result);
                                            }
                                            TryNum = 5;
                                            in.close();
                                            out.close();
                                            Client_socket.close();
                                        } catch (Exception e) {
                                            e.printStackTrace();
                                        }
                                        TryNum++;
                                    }//170911
                                    TryNum = 0;
									while (peerCount <= 0 && TryNum < 5) {//嘗試拿到最新的peerCount
										s_status = "State: acquiring the newest information at second phase";
										Log.d("Leaf0419", "State: acquiring the newest information");
										peerCount = count_peer(); 
										Thread.sleep(1000);
										sleep_time = sleep_time + 1000;
										TryNum++;
									}
									ROLE = RoleFlag.CLIENT.getIndex();//不論是原本就沒有身份得devcie或是被孤立的GO,都轉變為CLIEN的身份了
									STATE = StateFlag.GO_FORMATION.getIndex();
									 //s_status = "Become Client Time :" + ((Calendar.getInstance().getTimeInMillis() - start_time) / 1000) ;
									return;
								} else {
									STATE = StateFlag.ADD_SERVICE.getIndex();//如果wifi interface沒有連上表示可能資訊不夠新, 重add_service重新開始
								}
							}//End mNetworkInfo != null 
							else {
								STATE = StateFlag.ADD_SERVICE.getIndex();
								Log.d("Leaf0419", "State: associating GO, mNetworkInfo is null");
							}
						} else {
							STATE = StateFlag.ADD_SERVICE.getIndex();
							Log.d("Leaf0419", "State: associating GO, mConnectivityManager is null");
						}
					}//End ROLE=GO || ROLE=NONE
					else if (ROLE == RoleFlag.CLIENT.getIndex()) {//GO->Client之後在一次執行WiFi_Connect時會進入這裡. 才會去將p2p group移除
						relayIsconnect = false;
						//Log.d("Wang", "Come into Relay step");
						//relay_choose  maximum should be a random number to prevent two device connect each other at a same time slot
						if (relay_choose < 0) {
							Log.d("Wang", "Relay_choose < 0");
							relay_choose++;
							STATE = StateFlag.ADD_SERVICE.getIndex();
							return;
						} else {
							if(Collect_record.size() == 1) {//只有收集到1個device,這個device應該就只是自己(?)因此沒辦法當relay.只好回到ADD_SERVICE繼續蒐集資料
								Log.d("Wang", "Collect_record size == 1");
								STATE = StateFlag.ADD_SERVICE.getIndex();
								relay_choose = 0;
								return;
							}
							if (mNetworkInfo.isConnected() == false) {//wifi interface還沒連上別人(GO)
								Log.d("Wang", "mNetworkInfo.isConnected() == false");//可能原本有連上,所以ROLE==CLIENT,但之後可能wifi突然斷線了(?)
								relay_choose = 0;
								STATE = StateFlag.ADD_SERVICE.getIndex();
								return;
							}
							STATE = StateFlag.RELAY.getIndex();//收集到的資料>1,表示除了自己已經連上的GO以外還有其他裝置可以連線.//但是這個STATE在其他地方好像沒有用到唷!
							
							Collections.sort(Collect_record, new Step2Data_set_Comparator());//Collections根據step2的policy來排序
							MAC = GO_mac;
							//test
							String other_GO = "FALSE";
							for (int i = 0; i < Collect_record.size(); i++) {
								//other_GO test
								other_GO= Collect_record.get(i).getGO();//getGO裡面如果該筆紀錄的device自己是GO的話,則value=TRUE
								if(other_GO.equals("TRUE")) {
									if (!Collect_record.get(i).getName().equals(Cluster_Name)) {//不相等的話表示這個GO是屬於其他Cluster的,所以device可以連上他然後變成是relay連接兩個不同的cluster
										MAC = Collect_record.get(i).getMAC();
										Choose_Cluster_Name = Collect_record.get(i).getName();								
										break;
									}
								}
							}
							//test
							//170912
							if(!thisTimeMAC.equals(MAC)) {//這一次接收到device(其他)的MAC和接下來要連上的該device的MAC不同-?????????Miga 20180119不知道是不是為了確保資料是最新的(?)如果這次接收的info不是我們要連上的device傳來的,則reutrn
								STATE = StateFlag.ADD_SERVICE.getIndex();
								return;
							}
							if (MAC.equals(GO_mac)) {//可能是因為GO_mac和接下來要連接的cluster內的GO是一樣的,所以連了也沒用(因為已經連了，且連了也無法multi group)
								Log.d("Wang", "MAC.equals(GO_mac)");
								relay_choose = 0;
								STATE = StateFlag.ADD_SERVICE.getIndex();
								return;
							}
						   
							// 為了變成relay,需要先把自己的GO解除->讓要用p2p interface去連別人
							manager.removeGroup(channel, new WifiP2pManager.ActionListener() {
								@Override
								public void onSuccess() {
									Log.d("Wang", "remove group success");
								}

								@Override
								public void onFailure(int reason) {
									Log.d("Wang", "remove group fail");
								}
							});
							Thread.sleep(2000);
							sleep_time = sleep_time + 2;
							manager.stopPeerDiscovery(channel, new WifiP2pManager.ActionListener() {
								@Override
								public void onSuccess() {
									Log.d("Wang", "stopPeerDiscovery onSuccess");
									manager.discoverPeers(channel, new WifiP2pManager.ActionListener() {

										@Override
										public void onSuccess() {
											Log.d("Wang", "discoverPeers onSuccess");
										}

										@Override
										public void onFailure(int reasonCode) {
											Log.d("Wang", "discoverPeers onFailure");
										}
									});
								}

								@Override
								public void onFailure(int reasonCode) {
									Log.d("Wang", "stopPeerDiscovery onFailure");
								}
							});
							PreClusterName = Cluster_Name;
							Thread.sleep(5000);
							sleep_time = sleep_time + 5;
							
							WifiP2pConfig config = new WifiP2pConfig();
							config.deviceAddress = MAC;//設定接下來relay要連接的device的MAC address
							config.wps.setup = WpsInfo.PBC;
							config.groupOwnerIntent = 0;
							
							int try_num = 0;
							connect_check = false;
							
								s_status = "State: Relay associating GO, enable true:?" + MAC + " remainder #attempt:"
										+ try_num+ " Cluster_Name " + Choose_Cluster_Name ;
								Log.d("Wang", "State: Relay associating GO, enable true:?" + MAC + " remainder #attempt:"
										+ try_num+ " Cluster_Name " + Choose_Cluster_Name);
								//p2p interface去連別人
								manager.connect(channel, config, new ActionListener() {
									@Override
									public void onSuccess() {
										try {
											Thread.sleep(5000);
											sleep_time = sleep_time + 5;
										} catch (InterruptedException e) {
											// TODO Auto-generated catch block
											e.printStackTrace();
										}	
										ROLE = RoleFlag.RELAY.getIndex();//變為RELAY
										connect_check = true;
										Log.d("Wang", "P2P connect Success " + " " + "Cluseter_Name " + Cluster_Name);
										 try {
											 s_status = "peer_count time : " + Double.toString(((Calendar.getInstance().getTimeInMillis() - start_time) / 1000.0))   
											 +  " Round_Num :" + NumRound +" peer count : " + ServalDCommand.peerCount();
										} catch (ServalDFailureException e) {
											// TODO Auto-generated catch block
											e.printStackTrace();
										}
									}

									@Override
									public void onFailure(int reason) {//p2p interface連接失敗
										manager.cancelConnect(channel, new ActionListener() {
											@Override
											public void onSuccess() {}
											public void onFailure(int reason) {}
										});
										Log.d("Wang", "P2P connect failure");
									}							
								});
								try_num++;
								Thread.sleep(5000);
								sleep_time = sleep_time +5;
						
							if(ROLE != RoleFlag.RELAY.getIndex()) {
								ROLE = RoleFlag.CLIENT.getIndex();
								STATE = StateFlag.GO_FORMATION.getIndex();
								relay_choose = 0;
								return;
							}else if(ROLE == RoleFlag.RELAY.getIndex()){
								Cluster_Name = Choose_Cluster_Name;		
								relayIsconnect = true;//device已成為relay
							}
							 Log.d("Wang", " relayIsconnect " + relayIsconnect + "Cluster_Name "+ Choose_Cluster_Name + "PREROLE" + PreROLE + "ROLE" + "ROLE");
						}//End if relay_choose>=0
						//s_status = "Become Relay  : " + (Calendar.getInstance().getTimeInMillis() - start_time);
						relay_choose=0;
					} //End ROLE==CLIENT
					else {
						relay_choose=0;
					}
					
					if (  ROLE == RoleFlag.RELAY.getIndex()) {
						//Cluster_Name = WiFiApName;
						SimpleDateFormat sdf = new SimpleDateFormat("yyyy/MM/dd HH:mm:ss");
						Date dt=new Date();
						String timeStamp=sdf.format(dt);
						String[] firstArray = timeStamp.split(" ");
						String[] preArray = firstArray[0].split("/");
						String[] postArray = firstArray[1].split(":");

						int yearToSecond = Integer.valueOf(preArray[0]) * 365 * 24 * 60 * 60;
						int month = Integer.valueOf(preArray[1]);
						int monthToSecond = 0;
						int dayToSecond = Integer.valueOf(preArray[2]);
						//Log.d("Wang"," post " + postArray.toString() + " pre " + preArray.toString());
						for (int i = 1; i <= month; i++) {
							if ((i  == 1) || (i  == 3) || (i  == 5)
									|| (i  == 7) || (i  == 8) || (i  == 10)
									|| (i  == 12)) {
								monthToSecond += 31;
							} else if ((i  == 2) || (i  == 4) || (i  == 6)
									|| (i  == 9) || (i  == 11)) {
								monthToSecond += 30;
							} else {
								monthToSecond += 28;
							}
						}
						monthToSecond = monthToSecond * 24 * 60 * 60;
						dayToSecond = dayToSecond * 24 * 60 * 60;
						int hourToSecond = Integer.valueOf(postArray[0]);
						int minuteToSecond = Integer.valueOf(postArray[1]) ;
						int second = Integer.valueOf(postArray[2]);
						//Log.d("Wang","hour " + hourToSecond + " minute " + minuteToSecond + " second " + second + " " + Time_Stamp);
						Thread.sleep(5000);
						sleep_time = sleep_time +5;
						Time_Stamp =  monthToSecond + dayToSecond + hourToSecond + minuteToSecond
								+ second;
					}//End ROLE==RELAY
					if ( (PreROLE == RoleFlag.RELAY.getIndex() && ROLE == RoleFlag.CLIENT.getIndex())) {
						Cluster_Name = PreClusterName;
					}
					Log.d("Wang" ,"TimeStamp : "+Time_Stamp +"PREROLE " + PreROLE + " ROLE " + ROLE);
					STATE = StateFlag.ADD_SERVICE.getIndex();
				} //End ROLE==GO||NONE
				catch (Exception e) {
					STATE = StateFlag.ADD_SERVICE.getIndex();
					e.printStackTrace();
				}
			}
			catch (Exception e) {
				STATE = StateFlag.ADD_SERVICE.getIndex();
				e.printStackTrace();
			}
		}//End run
	}

	private void discoverService() {//發現附近裝置
		//使用setDnsSdResponseListeners監聽服務内容。
		manager.setDnsSdResponseListeners(channel, 
			new WifiP2pManager.DnsSdServiceResponseListener() {//接收Service
				@Override
				//Service Discovery 都會定期的發出 Bonjour，onDnsSdServiceAvailable表示Bonjour的回應被接收之後的行為，
				public void onDnsSdServiceAvailable(String instanceName, String registrationType, WifiP2pDevice srcDevice) { }
			    }, 
			new WifiP2pManager.DnsSdTxtRecordListener() {//接收Service後並解析收到的Service（可以檢查回應的服務內容是否是我們想要的資訊）
		    	@Override
				public void onDnsSdTxtRecordAvailable(String fullDomainName, Map<String, String> re_record,
						WifiP2pDevice device) {
		    		//有接收到其他device傳過來的info，所以才會近來這裡
					s_status = "State: advertising service, receive frame";
					Log.d("Leaf0419", "State: advertising service, receive frame");
					// Wang
					//re_record表示對方服務的內容
					record = re_record;
					
					if (t_wifi_connect == null) {
						//啟動 WiFi_Connect
						t_wifi_connect = new WiFi_Connect();
						t_wifi_connect.start();
					} else {
						if (!t_wifi_connect.isAlive()) {
							t_wifi_connect = new WiFi_Connect();
							t_wifi_connect.start();
						}
					}
					return;
			 }//End onDnsSdTxtRecordAvailable
		  });//End manager.setDnsSdResponseListeners();
		//用來創造Bonjour的request
		//Create a service discovery request to search all Bonjour services
		serviceRequest = WifiP2pDnsSdServiceRequest.newInstance();
	}//End discoverService
	
	private void startRegistration() {//讓別人發現我可以提供哪些服務,於Reconnection_wifiAP內的ADD_SERVICE呼叫近來
	     //  Create a string map containing information about your service.
		record_re = new HashMap();
		peerCount = count_peer();//計算peer的數量,計算PeerTable內有幾個不同的SSID
		updatePeerCount(peerCount);

		if (Cluster_Name == null) {
			Cluster_Name = WiFiApName;
		}
		if (Internet_Accessibility == null) {
			Internet_Accessibility = "intra";
		}
		//加入可提供給別人的服務
		record_re.put("Name", Cluster_Name);
		record_re.put("SSID", WiFiApName);
		record_re.put("PWD", GOpasswd);
		record_re.put("In_ac", Internet_Accessibility);
		record_re.put("PEER", String.valueOf(peerCount));

		// Wang
		record_re.put("MAC", GO_mac);
		// power level 一定要轉成 string
		record_re.put("POWER", Integer.toString(power_level));
		if(ROLE ==RoleFlag.GO.getIndex()){
			record_re.put("GO", "TRUE");
		}else {
			record_re.put("GO","FALSE");
		}

		s_status = "State: advertising service with " + record_re.toString() + " PREROLE " + PreROLE + " ROLE " + ROLE;
		Log.d("Leaf0419", "State: advertising service with " + record_re.toString());
		/* 
		 * Service information.  Pass it an instance name, service type
         * _protocol._transportlayer , and the map containing
         * information other devices will want once they connect to this one.
         */
		serviceInfo = WifiP2pDnsSdServiceInfo.newInstance("Wi-Fi_Info", "_presence._tcp", record_re);

		manager.clearLocalServices(channel, new WifiP2pManager.ActionListener() {//Clear all registered local services of service discovery. 
			@Override
			public void onSuccess() { 
		        /*
		         * Add the local service, sending the service info, network channel,
		         *	 and listener that will be used to indicate success or failure of the request.
		         */
				manager.addLocalService(channel, serviceInfo, new WifiP2pManager.ActionListener() {
					@Override
					public void onSuccess() {
						// service broadcasting started
						Log.d("Leaf0419", "State: advertising service, addLocalService onSuccess");
						manager.discoverPeers(channel, new WifiP2pManager.ActionListener() {//discoverPeers:開始對點(peer)的探索。A discovery process involves scanning for available Wi-Fi peers for the purpose of establishing a connection. 
				            @Override
				            public void onSuccess() {
				            	Log.d("Leaf0419", "State: discoverPeers onSuccess");
				            	STATE = StateFlag.DISCOVERY_SERVICE.getIndex();
				            }

				            @Override
				            public void onFailure(int error) {
				            }
						});//End discoverPeers
						STATE = StateFlag.DISCOVERY_SERVICE.getIndex();
					}//End addLocalService onSuccess

					@Override
					public void onFailure(int error) {
						Log.d("Leaf0419", "State: advertising service, addLocalService onFailure");
						STATE = StateFlag.ADD_SERVICE.getIndex();
					}//End addLocalService onFailure
				});//End addLocalService
			}//End clearLocalServices onSuccess

			@Override
			public void onFailure(int error) {
				Log.d("Leaf0419", "State: advertising service, clearLocalServices onFailure");
				STATE = StateFlag.ADD_SERVICE.getIndex();
			}//End clearLocalServices onFailure
		});//End clearLocalServices
	
	}//End startRegistration

	// Leaf1105
	//MAIN ,用來週期性的執行Service Discovery
	public class Reconnection_wifiAp extends Thread {
		ServerSocket GO_serversocket, Client_sersocket;
		Socket GO_socket, Client_socket;
		boolean can_I_connectAP;
		int TryNum;
		
		public void run() {
			//calculate the total time of connection
			
			while (isRunning) {//onCreate時將isRunnung設為true了
				try {
					Thread.sleep(1000);
					if (Auto) {//App 勾選Auto WFD之後會讓Auto變成true
						
						// print role
						//	s_status = "State: Role  : " + ROLE;
						//Log.d("Wang", "State: Role  : " + ROLE);
						if(ROLE != -1) {
							PreROLE = ROLE;//OnCreate時將ROLE=NONE=0;
						}
						if(start_time == 0) {//OnCreate時將start_time=0;
							start_time = Calendar.getInstance().getTimeInMillis();
							sleep_time = 0;
							discoverService();
						}
						if (STATE >= StateFlag.REMOVE_GROUP.getIndex())//REMOVE_GROUP=5
							continue;

						// Leaf0616
						if (STATE == StateFlag.DETECTGAW.getIndex()) {//Miga20180115 Wang 沒有用到, 可整段註解
							s_status = "State: detecting gateway";
							Log.d("Leaf0419", "State: detecting gateway");
							wifiScanCheck = false;
							wifi.startScan();
							while(wifiScanCheck == false) {};
							wifiScanCheck = false;
							
							/* Miga20180115 註解
							s_status = "State: detecting gateway done, can I connect to WMnet?: " + can_I_connectAP;
							Log.d("Leaf0419",
									"State: detecting gateway done, can I connect to WMnet?: " + can_I_connectAP);
							*/
							if (Isconnect == true) {//P2P interface
								STATE = StateFlag.ADD_SERVICE.getIndex();
							}
						}//END DETECTGAW
						
						if (Isconnect == false
								&& (ROLE == RoleFlag.GO.getIndex() || ROLE == RoleFlag.CLIENT.getIndex())) {
							STATE = StateFlag.GO_FORMATION.getIndex();
						} else {
							STATE = StateFlag.ADD_SERVICE.getIndex();
						}
						
						if (STATE == StateFlag.GO_FORMATION.getIndex()) {
							s_status = "State: creating GO in role" + ROLE;
							Log.d("Leaf0419", "State: creating GO");
							if (Isconnect == false) {//第一次建立GO(剛從NONE->GO(在WiFi_Connect內轉換))
								// SetGO
								if (ROLE == RoleFlag.GO.getIndex()) {
									Method setWifiP2pChannels;
									try {//更改go的channel
										int channel_to_set = 1;
										setWifiP2pChannels = manager.getClass().getMethod("setWifiP2pChannels", WifiP2pManager.Channel.class, int.class, int.class, WifiP2pManager.ActionListener.class);
										setWifiP2pChannels.invoke(manager, channel, 0, channel_to_set, new WifiP2pManager.ActionListener() {
										    @Override
										    public void onSuccess() {
										        Log.d("Wang", "Changed channel  succeeded");
										    }
										    @Override
										    public void onFailure(int reason) {
										        Log.d("Wang", "Changed channel failed");
										    }
										});
									} catch (NoSuchMethodException e2) {
										// TODO Auto-generated catch block
										e2.printStackTrace();
									} catch (IllegalAccessException e) {
										// TODO Auto-generated catch block
										e.printStackTrace();
									} catch (IllegalArgumentException e) {
										// TODO Auto-generated catch block
										e.printStackTrace();
									} catch (InvocationTargetException e) {
										// TODO Auto-generated catch block
										e.printStackTrace();
									}
								}
								
								if (ROLE == RoleFlag.GO.getIndex() || ROLE == RoleFlag.CLIENT.getIndex()) {
									if (manager != null) {//manager: WFD manager
										STATE = StateFlag.WAITING.getIndex();
										if(ROLE == RoleFlag.CLIENT.getIndex()) {//判斷client的wifi連線還存不存在
											mNetworkInfo = mConnectivityManager.getNetworkInfo(ConnectivityManager.TYPE_WIFI);//
											if (mNetworkInfo != null) {
												if(mNetworkInfo.isConnected() != true){//mNetworkInfo.isConnected() :判斷是否連接wifi網路
													//沒有連上wifi網路//Miga 20180117WIFI沒有連上的client?---->可能是原本有連成功,但之後可能斷線了
													STATE = StateFlag.GO_FORMATION.getIndex();
													continue;//跳回1654while迴圈
												}
											}
											Thread.sleep(1000);
										}//End ROLE==CLIENT
										
										Thread.sleep(1000);
										manager.createGroup(channel, new WifiP2pManager.ActionListener() {//不管是GO還是Client，都要以p2p 建立一個group。以讓其他人可以連上或是client在移除p2p然後連出去別的device
											@Override
											public void onSuccess() {//成功建立p2p group
												STATE = StateFlag.ADD_SERVICE.getIndex();//STATE從WAITING->ADD_SERVICE
												Log.d("Wang", "Isconnect : " + Isconnect);
												Isconnect = true;
												 s_status = "createGroup time : " + Double.toString(((Calendar.getInstance().getTimeInMillis() - start_time) / 1000.0))  +" stay_time : " +  Double.toString((sleep_time/1000.0)) 
												 +  " Round_Num :" + NumRound;
											
											}
											@Override
											public void onFailure(int error) {
												Log.d("Leaf0419", "createGroup onFailure");
												STATE = StateFlag.GO_FORMATION.getIndex();
											}
										});
									}//End manager!=null
								}//End GO||CLIENT
							} //End Isconnect==false
							else {//Isconnect==true
								STATE = StateFlag.ADD_SERVICE.getIndex();
							}
							continue;//跳回while迴圈
						}//End GO_FORMATION

						if (STATE == StateFlag.ADD_SERVICE.getIndex()) {
							s_status = "State: advertising service";
							Log.d("Leaf0419", "State: advertising service");
							STATE = StateFlag.WAITING.getIndex();
							if (Isconnect == true && ROLE == RoleFlag.NONE.getIndex()) {
								manager.removeGroup(channel, new WifiP2pManager.ActionListener() {
									@Override
									public void onSuccess() {
										Log.d("Wang", "remove group success");
									}
									@Override
									public void onFailure(int reason) {
										Log.d("Wang", "remove group fail");
									}
								});
							}
							long service_time = Calendar.getInstance().getTimeInMillis();
							startRegistration();
							sleep_time = sleep_time + Calendar.getInstance().getTimeInMillis() - service_time; 
							// 一定要 sleep 否則無法觸發discovery_service_flag
							// 造成一直執行 add_service_flag
							//while(addServiceCheck == false) {};
							//addServiceCheck =  false;
							Thread.sleep(2000);
							//if(t_wifi_connect.isAlive()) {
								sleep_time = sleep_time + 2000;
							//}
						}//End ADD_SERVICE
						
						if (STATE == StateFlag.DISCOVERY_SERVICE.getIndex()) {
							s_status = "State: discovering service";
							Log.d("Leaf0419", "State: discovering service");
							//stop在remove是因為peer discovery和service discovery衝突
							manager.stopPeerDiscovery(channel, new WifiP2pManager.ActionListener() {
								@Override
								public void onSuccess() {
									Log.d("Leaf0419", "State: discovering service, stopPeerDiscovery onSuccess");
									//於discoverService用來創造Bonjour的request
									//Create a service discovery request to search all Bonjour services
									//serviceRequest = WifiP2pDnsSdServiceRequest.newInstance();
									manager.removeServiceRequest(channel, serviceRequest,
											new WifiP2pManager.ActionListener() {
												@Override
												public void onSuccess() {
													manager.addServiceRequest(channel, serviceRequest,
															new WifiP2pManager.ActionListener() {
																@Override
																public void onSuccess() {
																	manager.discoverServices(channel,
																			new WifiP2pManager.ActionListener() {
																				@Override
																				public void onSuccess() {
																					Log.d("Leaf0419",
																							"State: discovering service, discoverServices onSuccess");
																					}//End discoverServices onSuccess

																				@Override
																				public void onFailure(int error) {
																					Log.d("Leaf0419",
																							"State: discovering service, discoverServices onFailure "
																									+ error);
																					manager.discoverPeers(channel,
																							null);
																					STATE = StateFlag.DETECTGAW
																							.getIndex();
																				}//End discoverServices onFailure
																			});//End discoverServices
																}//End addServiceRequest onSuccess

																@Override
																public void onFailure(int error) {
																	Log.d("Leaf0419",
																			"State: discovering service, addServiceRequest onFailure ");
																	STATE = StateFlag.DETECTGAW.getIndex();
																}//End addServiceRequest onFailure
															});//End addServiceRequest
												}//End removeServiceRequest onSuccess

												@Override
												public void onFailure(int reason) {
													Log.d("Leaf0419",
															"State: discovering service, removeServiceRequest onFailure");
													STATE = StateFlag.DETECTGAW.getIndex();
												}//End removeServiceRequest onFailure
											});//End removeServiceRequest
								}//End stopPeerDiscovery onSuccess

								@Override
								public void onFailure(int reasonCode) {
									Log.d("Leaf0419", "State: discovering service, stopPeerDiscovery onFailure");
									STATE = StateFlag.DETECTGAW.getIndex();
								}//End stopPeerDiscovery onFailure
							});//End stopPeerDiscovery


						manager.discoverPeers(channel, new WifiP2pManager.ActionListener() {
						        @Override
						        public void onSuccess() {
						        	Log.d("Wang", "peer discovery success");
						        }
						        @Override
						        public void onFailure(int reasonCode) {
						            switch(reasonCode){
							            case WifiP2pManager.ERROR:
							            	Log.d("Wang", "WifiP2pManager.ERROR");
							                break;
							
							            case WifiP2pManager.P2P_UNSUPPORTED:
							            	Log.d("Wang", "WifiP2pManager.P2P_UNSUPPORTED:");
							                break;					
							            case WifiP2pManager.BUSY:
							            	Log.d("Wang", "WifiP2pManager.BUSY:");
							                break;						
						            }
						        }
						    });
							//Thread.sleep(5000);
							//sleep_time = sleep_time + 5;

							if (STATE == StateFlag.DETECTGAW.getIndex()) {
								STATE = StateFlag.ADD_SERVICE.getIndex();
							} else if (STATE == StateFlag.DISCOVERY_SERVICE.getIndex()) {
								STATE = StateFlag.ADD_SERVICE.getIndex();
							}
						}//End DISCOVERY_SERVICE
						Thread.sleep(10000);
						sleep_time = sleep_time + 10000;
						NumRound++;
					}//End if(Auto)
				} catch (InterruptedException e) {
					e.printStackTrace();
				} catch (Exception e) {
					e.printStackTrace();
				} finally {
					if (Client_socket != null) {
						try {
							Client_socket.close();
						} catch (IOException e) {
							e.printStackTrace();
						}
					}
					if (Client_sersocket != null) {
						try {
							Client_sersocket.close();
						} catch (IOException e) {
							e.printStackTrace();
						}
					}
					if (GO_socket != null) {
						try {
							GO_socket.close();
						} catch (IOException e) {
							e.printStackTrace();
						}
					}
					if (GO_serversocket != null) {
						try {
							GO_serversocket.close();
						} catch (IOException e) {
							e.printStackTrace();
						}
					}
				}
			}//End While(isRunning)
		}//End run
	}//End Reconnection_wifiAp

	private String wifiIpAddress() {
		WifiManager wm = (WifiManager) getSystemService(WIFI_SERVICE);
		int ipAddress = wm.getConnectionInfo().getIpAddress();

		// Convert little-endian to big-endianif needed
		if (ByteOrder.nativeOrder().equals(ByteOrder.LITTLE_ENDIAN)) {
			ipAddress = Integer.reverseBytes(ipAddress);
		}

		byte[] ipByteArray = BigInteger.valueOf(ipAddress).toByteArray();

		String ipAddressString;
		try {
			ipAddressString = InetAddress.getByAddress(ipByteArray).getHostAddress();
		} catch (UnknownHostException ex) {
			Log.e("WIFIIP", "Unable to get host address.");
			ipAddressString = null;
		}

		return ipAddressString;
	}

	private int getForwardingPort() {
		String wlan0ip = wifiIpAddress();
		int lastDot = wlan0ip.lastIndexOf('.');
		int RightMostInt = Integer.valueOf(wlan0ip.substring(lastDot + 1));
		// Log.d("aqua0720", "IP rightest: "+RightMostInt);
		return RightMostInt + 10000;
	}
	// </aqua0722>

	// EditLeaf 0727
	// 此處應該要判斷連線可能中斷 造成重新連線 ip 不同 或是因為中斷 而造成其他裝置連線後 ip 相同的情況
	 public class CollectIP_server extends Thread {
	        private BufferedReader in;
	        private PrintWriter out;
	        private String message, temp;
	        private int i;

	        public void run() {
	            try {
	                ss = new ServerSocket(IP_port_for_IPModify);//建立一個ServerSocket並指定一個port監聽client的請求
	                while (true) {
	                    sc = ss.accept();//取的連線socket
	                    in = new BufferedReader(new InputStreamReader(sc.getInputStream()));//讀取client傳送的訊息
	                    message = in.readLine();
	                    Log.d("Leaf0419", "Receive IP: " + message);
	                    if (IPTable.containsKey(message)) {//IPTable內有這組IP
	                        temp = message;
	                        for (i = 2; i < 254; i++) {
	                            temp = "192.168.49." + String.valueOf(i);
	                            if (IPTable.containsKey(temp) == false) break;//重新產生新的IP
	                        }
	                        IPTable.put(temp, 0);//將新的IP存於IPTable
	                        message = "YES:" + temp;
	                    } else {//IPTable內沒有這組IP
	                        IPTable.put(message, 0);
	                        message = "NO:X";
	                    }
	                    out = new PrintWriter(sc.getOutputStream());
	                    out.println(message);//Server傳送message給Client
	                    Log.d("Leaf0419", "Send the message: " + message);
	                    out.flush();

	                    out.close();
	                    in.close();
	                    sc.close();
	                }

	            } catch (IOException e) {
	                Log.e(getClass().getName(), e.getMessage());
	            } finally {
	                try {
	                    if (in != null) {
	                        in.close();
	                    }
	                    if (out != null) {
	                        out.close();
	                    }
	                    if (sc != null) {
	                        sc.close();
	                    }
	                    if (ss != null) {
	                        ss.close();
	                    }
	                } catch (IOException e) {
	                    e.printStackTrace();
	                }
	            }
	        }
	    }

	// EditLeaf 0812
	public class Receive_peer_count extends Thread {
		private byte[] lMsg;
		private DatagramPacket receivedp, senddp;//Datagram是UDP
		private DatagramSocket sendds;
		private Iterator iterator;
		private String message, tempkey;
		private String[] temp;

		public void run() {
			lMsg = new byte[8192];
			receivedp = new DatagramPacket(lMsg, lMsg.length);//接收到的message會存在IMsg
			receiveds = null;

			try {
				receiveds = new DatagramSocket(IP_port_for_peer_counting);//接收的Socket
				// Wang add while condition
				int pre_peer_count = 0;
				while (IsNeedPeer) {//在OnCreate時設為true
					// for testing
					// ds.setSoTimeout(100000);
					receiveds.receive(receivedp);//把接收到的data存在receivedp
					message = new String(lMsg, 0, receivedp.getLength());//將接收到的IMsg轉換成String型態
					temp = message.split("#");//將message之中有#則分開存到tmep陣列裡;message = WiFiApName + "#" + Cluster_Name + "#" + "5";
					if (temp[0] != null && temp[1] != null && temp[2] != null && WiFiApName != null) {
						 //Log.d("Leaf0419", "Receive the message");
						// s_status = "State : Receive the message";
						// 0: source SSID 1: cluster name 2: TTL
						if (Newcompare(temp[0], WiFiApName) != 0) {//接收到的data和此裝置的SSID不同; 若A>B則reutrn 1
							// TTL -1
							temp[2] = String.valueOf(Integer.valueOf(temp[2]) - 1);//經過一個router因此-1
							// update peer table
							if (Newcompare(temp[1], Cluster_Name) == 0) {//相同Cluster_Name
								PeerTable.put(temp[0], 10);//填入收到data的SSID(WiFiApName)
								 if(count_peer() != pre_peer_count) {
									 pre_peer_count = count_peer();//更新現在PeerTable內有幾個Peer
									 s_status = "peer_count time : " + Double.toString(((Calendar.getInstance().getTimeInMillis() - start_time) / 1000.0))  +" stay_time : " +  Double.toString((sleep_time/1000.0)) 
									 +  " Round_Num :" + NumRound +" peer count : "  + ServalDCommand.peerCount();
								 }
							}
							// relay packet
							if (Integer.valueOf(temp[2]) > 0) {
								message = temp[0] + "#" + temp[1] + "#" + temp[2];
								sendds = null;
								sendds = new DatagramSocket();
								// broadcast
								senddp = new DatagramPacket(message.getBytes(), message.length(),
										InetAddress.getByName("192.168.49.255"), IP_port_for_peer_counting);
								sendds.send(senddp);
							//	Log.d("Leaf0419", "(Relay)Send the message: " + message + " to broadcast");
								// s_status = "State : (Relay)Send the message:
								// " + message + " to broadcast";
								// unicast
								iterator = IPTable.keySet().iterator();
								while (iterator.hasNext()) {
									tempkey = iterator.next().toString();
									senddp = new DatagramPacket(message.getBytes(), message.length(),
											InetAddress.getByName(tempkey), IP_port_for_peer_counting);
									sendds.send(senddp);
								//	Log.d("Leaf0419", "(Relay)Send the message: " + message + " to " + tempkey);
									// s_status = "State : (Relay)Send the
									// message: " + message + " to " + tempkey;
									
								}
								//for relay
								senddp = new DatagramPacket(message.getBytes(), message.length(),
										InetAddress.getByName("192.168.49.1"), IP_port_for_peer_counting);
								sendds.send(senddp);
								
								sendds.close();
							}

						}
					}
				}
			} catch (SocketException e) {
				e.printStackTrace();
				Log.d("Wang", "Receive_peer_count Socket exception" + e.toString());
			} catch (IOException e) {
				e.printStackTrace();
				Log.d("Wang", "Receive_peer_count IOException" + e.toString());
			} catch (Exception e) {
				e.printStackTrace();
				Log.d("Wang", "Receive_peer_count Exception" + e.toString());
			} finally {
				if (receiveds != null) {
					receiveds.close();
					 Log.d("Wang", "Receive_peer_count receiveds is close");
				}
				if (sendds != null) {
					sendds.close();
					Log.d("Wang", "Receive_peer_count sendds is close");
				}
			}
		}
	}

	// EditLeaf0812
	public int count_peer() {//計算PeerTable內有幾個不同的SSID
		// By Leaf
		int result = 0;
		Iterator iterator = PeerTable.keySet().iterator();//Send_peer_count和Receive_peer_count內會去新增/刪除PeerTable
		String tempkey;
		while (iterator.hasNext()) {
			tempkey = iterator.next().toString();
			result++;
		}
		//Log.d("Leaf0419", "The peer count result is : " + result);
		// By Serval Mesh
		/*
		 * try { result = ServalDCommand.peerCount(); }catch
		 * (ServalDFailureException e) { e.printStackTrace(); }
		 */
		return result;
	}

	// EditLeaf 0812
	public class Send_peer_count extends Thread {
		private DatagramPacket dp;
		private DatagramSocket sendds;
		private Iterator iterator;
		private String message, tempkey;

		public void run() {
			try {
				sendds = null;
				sendds = new DatagramSocket();
				// Wang add while condition
				while (IsNeedPeer) {
					try {
						if (Isconnect || relayIsconnect) {
							message = WiFiApName + "#" + Cluster_Name + "#" + "5";// 0: source SSID 1: cluster name 2: TTL
							// broadcast
							dp = new DatagramPacket(message.getBytes(), message.length(),
									InetAddress.getByName("192.168.49.255"), IP_port_for_peer_counting);
							sendds.send(dp);
							//Log.d("Leaf0419", "(Proactive)Send the message: " + message + " to broadcast");
							// s_status = "State : (Proactive)Send the message:
							// " + message + " to broadcast";
							
							
							// unicast
							iterator = IPTable.keySet().iterator();//IPTable的keySet為許多IP所組成
							while (iterator.hasNext()) {
								tempkey = iterator.next().toString();
								dp = new DatagramPacket(message.getBytes(), message.length(),
										InetAddress.getByName(tempkey), IP_port_for_peer_counting);
								sendds.send(dp);//一一傳送給IPTable內的所有IP
								//Log.d("Leaf0419", "(Proactive)Send the message: " + message + " to " + tempkey);
								// s_status = "State : (Proactive)Send the
								// message: " + message + " to " + tempkey;
							}
							
							//for relay
							dp = new DatagramPacket(message.getBytes(), message.length(),
									InetAddress.getByName("192.168.49.1"), IP_port_for_peer_counting);
							sendds.send(dp);//傳給GO

							// update peer table
							iterator = PeerTable.keySet().iterator();
							while (iterator.hasNext()) {
								tempkey = iterator.next().toString();
								PeerTable.put(tempkey, PeerTable.get(tempkey) - 1);//一一把PeerTable內對應到的SSID的value-1
								if (PeerTable.get(tempkey) <= 0) {//value值
									PeerTable.remove(tempkey);//將此SSID移除
								}
							}
						}
						count_peer();//計算PeerTable內不同SSID的數量
					} catch (Exception e) {
						e.printStackTrace();
						//Log.d("Wang", "Send_IsNeedPeer  exception" + e.toString());
					}
					Thread.sleep(1000);
				}
			} catch (SocketException e) {
				e.printStackTrace();
				Log.d("Wang", "Send_peer_count Socket exception" + e.toString());
			} catch (IOException e) {
				e.printStackTrace();
				Log.d("Wang", "Send_peer_count IOException" + e.toString());
			} catch (InterruptedException e) {
				e.printStackTrace();
				Log.d("Wang", "Send_peer_count InterruptedException" + e.toString());
			} catch (Exception e) {
				e.printStackTrace();
				Log.d("Wang", "Send_peer_count other exception" + e.toString());
			} finally {
				if (sendds != null) {
					sendds.close();
					Log.d("Wang", "Send_peer_count sendds is close");
				}
			}
		}
	}
	public class Receive_cluster_name extends Thread {
		private byte[] lMsg;
		private DatagramPacket receivedp, senddp;
		private DatagramSocket sendds;
		private Iterator iterator;
		private String message, tempkey;
		private String[] temp;

		private boolean  check;
		private int m_length = 0;
		
		public void run() {
			lMsg = new byte[8192];
			receivedp = new DatagramPacket(lMsg, lMsg.length);
			receiveds_cluster = null;
			try {
				receiveds_cluster = new DatagramSocket(IP_port_for_cluster_name);

				while (IsNeedClusterName) {
					Thread.sleep(500);
					receiveds_cluster.receive(receivedp);
					if (receivedp == null) {
						continue;
					}
					message = new String(lMsg, 0, receivedp.getLength());
					temp = message.split("#");
					m_length = temp.length;
					check=  true;
					for(int i = 0; i < m_length; i++) {
						if(temp[i] != null && !temp[i].isEmpty() && !temp[i].equals("null")) {
						}else {
							check = false;
							break;
						}
					}
					if(check == true){
						if (Newcompare(temp[0], WiFiApName) != 0) {
							temp[5] = String.valueOf(Integer.valueOf(temp[5]) - 1);
							// update peer table
							if (IsInitial) {
								if (ROLE == RoleFlag.NONE.getIndex() || ROLE == RoleFlag.RELAY.getIndex()
										|| ROLE == RoleFlag.CLIENT.getIndex()
										|| ROLE == RoleFlag.WIFI_CLIENT.getIndex()) {
									if (Integer.valueOf(temp[2]) == RoleFlag.GO.getIndex()) {
										if (IsReceiveGoInfo==false) {
											Cluster_Name = temp[1];
										} else {
											if (Newcompare(Cluster_Name, temp[1]) <= 0) {
												Cluster_Name = temp[1];
											} else {
											}
										}
										IsReceiveGoInfo = true;
									}else if (Integer.valueOf(temp[2]) == RoleFlag.RELAY.getIndex() ||(Integer.valueOf(temp[2]) == RoleFlag.CLIENT.getIndex() )){
										if(ROLE == RoleFlag.CLIENT.getIndex()){
											if(IsReceiveGoInfo == true) {
												ROLE =RoleFlag.GO.getIndex();
											}
										}
									}
								}
							} else {
								if (Integer.valueOf(temp[2]) == RoleFlag.GO.getIndex()) {
									IsReceiveGoInfo = true;
								}else if (Integer.valueOf(temp[2]) == RoleFlag.RELAY.getIndex() ||(Integer.valueOf(temp[2]) == RoleFlag.CLIENT.getIndex() )){
									if(ROLE == RoleFlag.CLIENT.getIndex()){
										if(IsReceiveGoInfo == true) {
											clientACK= true;
										}
									}
								}
								int Other_Time_Stamp = Integer.valueOf(temp[4]);
								if (Other_Time_Stamp > Time_Stamp) {
									Cluster_Name = temp[1];
									Time_Stamp = Other_Time_Stamp;
								}
							}
						}
					}
				}
			} catch (SocketException e) {
				e.printStackTrace();
				Log.d("Wang", "Receive_cluster_name Socket exception" + e.toString());
			} catch (IOException e) {
				e.printStackTrace();
				Log.d("Wang", "Receive_cluster_name IOException");
			} catch (Exception e) {
				e.printStackTrace();
				Log.d("Wang", "Receive_cluster_name other exception" + e.toString());
			} finally {
				if (receiveds_cluster != null) {
					receiveds_cluster.close();
					Log.d("Wang", "Receive_cluster_name receiveds_cluster is close");
				}
			}
		}
	}

	public class Send_cluster_name extends Thread {
		private DatagramPacket dp;
		private DatagramSocket sendds;
		private Iterator iterator;
		private String message, tempkey;

		public void run() {
			try {
				sendds = null;
				sendds = new DatagramSocket();
				while (IsNeedClusterName) {
					try {
						if (Isconnect || relayIsconnect) {
							message = WiFiApName + "#" + Cluster_Name + "#" + ROLE + "#" + IsReceiveGoInfo + "#"
									+ Time_Stamp + "#" + "5";
							if (WiFiApName == null || Cluster_Name == null) {
								continue;
							}
							// broadcast
							dp = new DatagramPacket(message.getBytes(), message.length(),
									InetAddress.getByName("192.168.49.255"), IP_port_for_cluster_name);
							sendds.send(dp);
							// broadcast";
							Thread.sleep(1000);
							// unicast
							iterator = IPTable.keySet().iterator();
							while (iterator.hasNext()) {
								tempkey = iterator.next().toString();
								dp = new DatagramPacket(message.getBytes(), message.length(),
										InetAddress.getByName(tempkey), IP_port_for_cluster_name);
								sendds.send(dp);
								Thread.sleep(1000);
							}
							//for relay
							dp = new DatagramPacket(message.getBytes(), message.length(),
									InetAddress.getByName("192.168.49.1"), IP_port_for_peer_counting);
							sendds.send(dp);
						}
					} catch (Exception e) {
						e.printStackTrace();
						Log.d("Wang", "Send_IsNeedClusterName Exception" + e.toString());
					}
					Thread.sleep(1000);
				}
			} catch (SocketException e) {
				e.printStackTrace();
				Log.d("Wang", "Send_cluster_name SocketException" + e.toString());
			} catch (IOException e) {
				e.printStackTrace();
				Log.d("Wang", "Send_cluster_name IOException" + e.toString());
			} catch (InterruptedException e) {
				e.printStackTrace();
				Log.d("Wang", "Send_cluster_name InterruptedException" + e.toString());
			} catch (Exception e) {
				e.printStackTrace();
				Log.d("Wang", "Send_cluster_name other exception" + e.toString());
			} finally {
				if (sendds != null) {
					sendds.close();
					Log.d("Wang", "Send_cluster_name sendds is close");
				}
			}
		}
	}
/*
	// wang update cluster name (receive)
	//主要再做Cluster_Name的更新(比較字典序,長度)
	public class Receive_cluster_name extends Thread {
		private byte[] lMsg;
		private DatagramPacket receivedp, senddp;
		private DatagramSocket sendds;
		private Iterator iterator;
		private String message, tempkey;
		private String[] temp;

		private boolean  check;
		private int m_length = 0;
		
		public void run() {
			lMsg = new byte[8192];
			receivedp = new DatagramPacket(lMsg, lMsg.length);
			receiveds_cluster = null;
			try {
				receiveds_cluster = new DatagramSocket(IP_port_for_cluster_name);

				// Wang add while condition
				while (IsNeedClusterName) {//OnCreate時就設為true
					Thread.sleep(500);
					// for testing
					// ds.setSoTimeout(100000);
					receiveds_cluster.receive(receivedp);//receivedp是儲存收到的data
					if (receivedp == null) {
						continue;//下面不執行,回到while迴圈
					}
					message = new String(lMsg, 0, receivedp.getLength());
					//Log.d("Miga", "Receive_Cluster_Name: message"+message);
					//s_status="Receive CN"+message;
					temp = message.split("#");// WiFiApName + "#" + Cluster_Name + "#" + ROLE + "#" + IsReceiveGoInfo + "#"+ Time_Stamp + "#" + "5";
					m_length = temp.length;
					check=  true;
					for(int i = 0; i < m_length; i++) {
						if(temp[i] != null && !temp[i].isEmpty() && !temp[i].equals("null")) {
						}else {
							check = false;
							break;
						}
					}//End for
					if(check == true){
						//Log.d("Wang_clusterName", "Receive the message");
						if (Newcompare(temp[0], WiFiApName) != 0) {
							//Log.d("Wang_clusterName", "Receive the message from others ");
							// TTL -1
							temp[5] = String.valueOf(Integer.valueOf(temp[5]) - 1);
							// update peer table
							if (IsInitial) {
								if (ROLE == RoleFlag.NONE.getIndex() || ROLE == RoleFlag.RELAY.getIndex()
										|| ROLE == RoleFlag.CLIENT.getIndex() || ROLE == RoleFlag.WIFI_CLIENT.getIndex()) {//此裝置不是GO角色
									if (Integer.valueOf(temp[2]) == RoleFlag.GO.getIndex()) {//收到的data是GO
										if (IsReceiveGoInfo==false) {
											Cluster_Name = temp[1];//把自己的Cluster_Name更新成GO的Cluster_Name
										} else {//已經接收過GO的data
											if (Newcompare(Cluster_Name, temp[1]) <= 0) {//此裝置的Cluster_Name字典序或是長度比這次收到的data(GO)還小
												Cluster_Name = temp[1];//更新成比較大的Cluster_Name
											} else {
												//temp[1] = Cluster_Name;
											}
										}
										IsReceiveGoInfo = true;
									}//End temp[2]==GO
									else if (Integer.valueOf(temp[2]) == RoleFlag.RELAY.getIndex() ||(Integer.valueOf(temp[2]) == RoleFlag.CLIENT.getIndex() )){
										if(ROLE == RoleFlag.CLIENT.getIndex()){
											if(IsReceiveGoInfo == true) {//已經接收過GO的data了,因此自己的device的ROLE變為GO.(這種應該是Connected GO的第二張圖中間device的情況)
												ROLE =RoleFlag.GO.getIndex();
											}
										}
									}//End temp[2]==RELAY||CLIENT
								}//End ROLE==NONE||RELAY||CLIENT||WIFI_CLIENT 
							}//End Isinitial
							else {//170907不懂Isinitial是否為true&false的差別
								if (Integer.valueOf(temp[2]) == RoleFlag.GO.getIndex()) {//接收到的info是從GO傳送來的
									IsReceiveGoInfo = true;
								}else if (Integer.valueOf(temp[2]) == RoleFlag.RELAY.getIndex() ||(Integer.valueOf(temp[2]) == RoleFlag.CLIENT.getIndex() )){
									if(ROLE == RoleFlag.CLIENT.getIndex()){
										if(IsReceiveGoInfo == true) {
											clientACK= true;
										}
									}
								}
								int Other_Time_Stamp = Integer.valueOf(temp[4]);
								if (Other_Time_Stamp > Time_Stamp) {//對方的time_stamp比較新
									Cluster_Name = temp[1];
									Time_Stamp = Other_Time_Stamp;
								}
							}
						}
					}
				}
			} catch (SocketException e) {
				e.printStackTrace();
				Log.d("Wang", "Receive_cluster_name Socket exception" + e.toString());
			} catch (IOException e) {
				e.printStackTrace();
				Log.d("Wang", "Receive_cluster_name IOException");
			} catch (Exception e) {
				e.printStackTrace();
				Log.d("Wang", "Receive_cluster_name other exception" + e.toString());
			} finally {
				if (receiveds_cluster != null) {
					receiveds_cluster.close();
					Log.d("Wang", "Receive_cluster_name receiveds_cluster is close");
				}
			}
		}
	}

	// wang update cluster name (send)
	public class Send_cluster_name extends Thread {
		private DatagramPacket dp;
		private DatagramSocket sendds;
		private Iterator iterator;
		private String message, tempkey;

		public void run() {
			try {
				sendds = null;
				sendds = new DatagramSocket();
				// Wang add while condition
				while (IsNeedClusterName) {
					try {
						if (Isconnect || relayIsconnect) {
							message = WiFiApName + "#" + Cluster_Name + "#" + ROLE + "#" + IsReceiveGoInfo + "#"
									+ Time_Stamp + "#" + "5";//Time_Stamp是在wifi_connect內設定的
							//Log.d("Miga", "Send_Cluster_Name message:"+message);
							if (WiFiApName == null || Cluster_Name == null) {
								//Log.d("Miga", "WiFiApName == null || Cluster_Name == null");
								continue;
							}
							 //Log.d("Wang_clusterName", message);
							// broadcast
							dp = new DatagramPacket(message.getBytes(), message.length(),
									InetAddress.getByName("192.168.49.255"), IP_port_for_cluster_name);
							sendds.send(dp);
							//Log.d("Miga", "(Proactive)Send th ClusterName message: " + message + " to broadcast");
							 //Log.d("Wang clusterName", "(Proactive)Send th ClusterName message: " + message + " to broadcast");
							
							// s_status = "State : (Proactive)Send the
							// ClusterName message: " + message + " to
							// broadcast";
							Thread.sleep(1000);
							// unicast
							iterator = IPTable.keySet().iterator();
							while (iterator.hasNext()) {
								tempkey = iterator.next().toString();
								dp = new DatagramPacket(message.getBytes(), message.length(),
										InetAddress.getByName(tempkey), IP_port_for_cluster_name);
								sendds.send(dp);
								// Log.d("Wang clusterName", "(Proactive)Send
								// the ClusterName message: " + message + " to "
								// + tempkey);
								// s_status = "State : (Proactive)Send the
								// ClusterName message: " + message + " to " +
								// tempkey;
								Thread.sleep(1000);
							}
							//for relay
							dp = new DatagramPacket(message.getBytes(), message.length(),
									InetAddress.getByName("192.168.49.1"), IP_port_for_cluster_name);//170907以前是IP_port_for_peer_counting
							sendds.send(dp);
						}//End Isconnect || relayIsconnect
						//else{
							//Log.d("Miga", "Isconnect || relayIsconnect==false");}
					} catch (Exception e) {
						e.printStackTrace();
						Log.d("Wang", "Send_IsNeedClusterName Exception" + e.toString());
					}
					Thread.sleep(1000);
				}//End IsNeedClusterName
			} catch (SocketException e) {
				e.printStackTrace();
				Log.d("Wang", "Send_cluster_name SocketException" + e.toString());
			} catch (IOException e) {
				e.printStackTrace();
				Log.d("Wang", "Send_cluster_name IOException" + e.toString());
			} catch (InterruptedException e) {
				e.printStackTrace();
				Log.d("Wang", "Send_cluster_name InterruptedException" + e.toString());
			} catch (Exception e) {
				e.printStackTrace();
				Log.d("Wang", "Send_cluster_name other exception" + e.toString());
			} finally {
				if (sendds != null) {
					sendds.close();
					Log.d("Wang", "Send_cluster_name sendds is close");
				}
			}
		}
	}
*/
	@Override
	//onCreate表示事情只做一次用來initail，onStartCommand表示會執行很多次，先執行 onCreate 再執行 onStartCommand
	public void onCreate() {
		// Leaf0818
		Log.d("Leaf1110", "Control_onCreate()");
		this.app = (ServalBatPhoneApplication) this.getApplication();
		PowerManager pm = (PowerManager) app.getSystemService(Context.POWER_SERVICE);
		cpuLock = pm.newWakeLock(PowerManager.PARTIAL_WAKE_LOCK, "Services");
		super.onCreate();
		// intentfilter 用來判斷接收到哪個intent要執行相對應的動作	
 		intentFilter.addAction(WifiP2pManager.WIFI_P2P_STATE_CHANGED_ACTION);//  Indicates a change in the Wi-Fi P2P status.
        intentFilter.addAction(WifiP2pManager.WIFI_P2P_PEERS_CHANGED_ACTION);// Indicates a change in the list of available peers.
        intentFilter.addAction(WifiP2pManager.WIFI_P2P_CONNECTION_CHANGED_ACTION);//// Indicates the state of Wi-Fi P2P connectivity has changed.
        intentFilter.addAction(WifiP2pManager.WIFI_P2P_THIS_DEVICE_CHANGED_ACTION); // Indicates this device's details have changed.
		manager = (WifiP2pManager) getSystemService(Context.WIFI_P2P_SERVICE);
		channel = manager.initialize(this, getMainLooper(), null);
		// Leaf1201
		wifi = (WifiManager) getSystemService(Context.WIFI_SERVICE);
		// Leaf1202
		//用來管理網路連線狀態
		mConnectivityManager = (ConnectivityManager) getSystemService(Context.CONNECTIVITY_SERVICE);
		// Leaf0616
		/*
		 * 註冊廣播接收器: registerReceiver(mMyReceiver, itFilter);
		 * 當有人sendBroadcast 其 intent為
		 * WifiManager.SCAN_RESULTS_AVAILABLE_ACTION 則觸發
		 * SCAN_RESULTS_AVAILABLE_ACTION:An access point scan has completed, and results are available from the supplicant.
         */
		registerReceiver(receiver_scan = new BroadcastReceiver() {
			@Override
			//得到 initail scan 的結果
			public void onReceive(Context c, Intent intent) {
				wifi_scan_results = wifi.getScanResults();//getScanResults: the list of access points found in the most recent scan
				result_size = wifi_scan_results.size();
				wifiScanCheck = true;//執行完wifi scan後
			//Log.d("wang", "State: detecting gateway, get the scan result" + wifi_scan_results.toString());
			}
		}, new IntentFilter(WifiManager.SCAN_RESULTS_AVAILABLE_ACTION));//在wifi.startScan()完畢後就會觸發此receiver()

		// Experiment
		NumRound = 1;
		sleep_time = 0;
		total_time = 0;
		start_time = 0;
		initial_start_time = 0;
		other_time = 0;

		// Wang
		Collect_record = new ArrayList<Step1Data_set>();
		this.registerReceiver(this.mBatInfoReceiver, new IntentFilter(Intent.ACTION_BATTERY_CHANGED));
		//record_set = new ArrayList<Map>();
		ROLE = RoleFlag.NONE.getIndex();
		IsNeedPeer = true;
		IsReceiveGoInfo = false;
		IsNeedClusterName = true;
		// Get Go Info
		if (initial == null) {
			initial = new Initial();
			initial.start();
		}
		callAsynchronousTask();
		/*
		 * WiFiApName = "talk"; Cluster_Name = "gudi";
		 */

	}

	private BroadcastReceiver mBatInfoReceiver = new BroadcastReceiver() {
		@Override
		public void onReceive(Context ctxt, Intent intent) {
			int level = intent.getIntExtra(BatteryManager.EXTRA_LEVEL, 0);
			power_level = level;
		}
	};

	@Override
	public void onDestroy() {
		Log.d("Leaf1110", "Control Services Destroy");
		new Task().execute(State.Off);
		app.controlService = null;
		serviceRunning = false;
		if (receiver != null)
			unregisterReceiver(receiver);
		if (receiver_scan != null)
			unregisterReceiver(receiver_scan);
		isRunning = false;
		if (t_findPeer != null)
			t_findPeer.interrupt();
		if (t_checkGO != null)
			t_checkGO.interrupt();
		if (t_reconnection_wifiAp != null)
			t_reconnection_wifiAp.interrupt();
		if (t_collectIP != null)
			t_collectIP.interrupt();
		if (t_send_peer_count != null)
			t_send_peer_count.interrupt();
		if (t_receive_peer_count != null)
			t_receive_peer_count.interrupt();

		// wang
		if (t_send_cluster_name != null) {
			t_send_cluster_name.interrupt();
		}
		if (t_receive_cluster_name != null) {
			t_receive_cluster_name.interrupt();
		}
		if (receiveds_cluster != null) {
			receiveds_cluster.close();
		}

		if (initial != null) {
			initial.interrupt();
		}
		t_send_cluster_name = null;
		t_receive_cluster_name = null;
		initial = null;

		// <aqua0722>
		/*
		 * if (t_native != null) t_native.interrupt(); if (t_register != null)
		 * t_register.interrupt();
		 * 
		 * t_native = null; t_register = null;
		 */
		// </aqua0722>
		receiver = null;
		t_findPeer = null;
		t_checkGO = null;
		t_reconnection_wifiAp = null;
		t_collectIP = null;
		t_send_peer_count = null;
		t_receive_peer_count = null;
		if (receiveds != null)
			receiveds.close();
		try {
			if (sc != null)
				sc.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
		if (manager != null && serviceInfo != null && serviceRequest != null) {
			manager.removeLocalService(channel, serviceInfo, null);
			manager.removeServiceRequest(channel, serviceRequest, null);
			manager.clearLocalServices(channel, null);
			manager.clearServiceRequests(channel, null);
		}

		// EditLeaf0802
		try {
			if (ss != null)
				ss.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
		super.onDestroy();
	}

	@Override
	public int onStartCommand(Intent intent, int flags, int startId) {
		// Leaf0818
		Log.d("Leaf1110", "Control Services StartCommand");
		//拿取現在serval_mesh這個app的狀態
		State existing = app.getState();
		// Don't attempt to start the service if the current state is invalid
		// (ie Installing...)
		if (existing != State.Off && existing != State.On) {
			Log.v("Control", "Unable to process request as app state is " + existing);
			return START_NOT_STICKY;
		}
		if (receiver == null) {
			//註冊一個broadcast的接收者，聽到 intent 告訴 AutoWiFiDirect 做相對應的事
			//需要去找sendBroadcast()由誰呼叫出??
			receiver = new AutoWiFiDirect(manager, channel, this, Isconnect, myDeviceName);
			registerReceiver(receiver, intentFilter);
		}
		//開啟自訂的連線機制
		isRunning = true;
		if (t_reconnection_wifiAp == null) {
			t_reconnection_wifiAp = new Reconnection_wifiAp();//
			t_reconnection_wifiAp.start();
		}
		if (t_collectIP == null) {
			t_collectIP = new CollectIP_server();
			t_collectIP.start();
		}

		// Following two threads is for counting peers by our module,
		// since Serval Mesh has already supported a similar function,
		// you can decide whether utilized following code

		if (t_send_peer_count == null) {
			t_send_peer_count = new Send_peer_count();
			t_send_peer_count.start();
		}
		if (t_receive_peer_count == null) {
			t_receive_peer_count = new Receive_peer_count();
			t_receive_peer_count.start();
		}

		// wang
		if (t_send_cluster_name == null) {
			t_send_cluster_name = new Send_cluster_name();
			t_send_cluster_name.start();
		}

		if (t_receive_cluster_name == null) {
			t_receive_cluster_name = new Receive_cluster_name();
			t_receive_cluster_name.start();
		}

		// <aqua0722>
		/*
		 * if (t_native == null) { t_native = new NativeCall();
		 * t_native.start(); } if (t_register == null) { t_register = new
		 * RegisterToServer(); t_register.start(); }
		 */

		

		// </aqua0722>
		//執行 notification的任務
		new Task().execute(State.On);
		//開啟serval_mesh服務
		serviceRunning = true;
		//將狀態設成 detectGateway
		STATE = StateFlag.DETECTGAW.getIndex();
		return START_STICKY;
	}

	@Override
	public IBinder onBind(Intent arg0) {
		return mBinder;
	}

	public class MyBinder extends Binder {
		public Control getService() {
			return Control.this;
		}
	}

	// Following code is for setting static IP address
	private boolean setIpWithTfiStaticIp(String IP) {
		WifiConfiguration wifiConfig = null;
		WifiInfo connectionInfo = wifi.getConnectionInfo();

		List<WifiConfiguration> configuredNetworks = wifi.getConfiguredNetworks();
		for (WifiConfiguration conf : configuredNetworks) {
			if (conf.networkId == connectionInfo.getNetworkId()) {
				wifiConfig = conf;
				break;
			}
		}
		try {
			
			setStaticIpConfiguration(wifi, wifiConfig, InetAddress.getByName(IP), 24, InetAddress.getByName(IP), InetAddress.getAllByName(IP));  
			/*setIpAssignment("STATIC", wifiConfig);
			setIpAddress(InetAddress.getByName(IP), 24, wifiConfig);
			wifi.updateNetwork(wifiConfig); // apply the setting*/
			
			return true;
		} catch (Exception e) {
			e.printStackTrace();
			Log.d("Wang", "setIpWithTfiStaticIp " + e.toString());
			return false;
		}
	}

	private static void setIpAssignment(String assign, WifiConfiguration wifiConf)
			throws SecurityException, IllegalArgumentException, NoSuchFieldException, IllegalAccessException {
		try {
			Object ipConfiguration = wifiConf.getClass().getMethod("getIpConfiguration").invoke(wifiConf);
			setEnumField(ipConfiguration, assign, "ipAssignment");
		} catch (InvocationTargetException e) {
			// TODO Auto-generated catch block
			
			e.printStackTrace();
			Log.d("Wang", "setIpAssignment " + e.toString());
		} catch (NoSuchMethodException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			Log.d("Wang", "setIpAssignment " + e.toString());
		}
		//setEnumField(wifiConf, assign, "ipAssignment");
		
	}

	private static void setIpAddress(InetAddress addr, int prefixLength, WifiConfiguration wifiConf)
			throws SecurityException, IllegalArgumentException, NoSuchFieldException, IllegalAccessException,
			NoSuchMethodException, ClassNotFoundException, InstantiationException, InvocationTargetException {
		//Object ipConfiguration = wifiConf.getClass().getMethod("getIpConfiguration").invoke(wifiConf);
		//Object linkProperties = getField(ipConfiguration, "linkProperties");
		Object linkProperties = getField(wifiConf, "linkProperties");
		if (linkProperties == null)
			return;
		Class<?> laClass = Class.forName("android.net.LinkAddress");
		Constructor<?> laConstructor = laClass.getConstructor(new Class[] { InetAddress.class, int.class });
		Object linkAddress = laConstructor.newInstance(addr, prefixLength);

		ArrayList<Object> mLinkAddresses = (ArrayList<Object>) getDeclaredField(linkProperties, "mLinkAddresses");
		mLinkAddresses.clear();
		mLinkAddresses.add(linkAddress);
	}

	private static Object getField(Object obj, String name)
			throws SecurityException, NoSuchFieldException, IllegalArgumentException, IllegalAccessException {
		Field f = obj.getClass().getField(name);
		Object out = f.get(obj);
		return out;
	}

	private static Object getDeclaredField(Object obj, String name)
			throws SecurityException, NoSuchFieldException, IllegalArgumentException, IllegalAccessException {
		Field f = obj.getClass().getDeclaredField(name);
		f.setAccessible(true);
		Object out = f.get(obj);
		return out;
	}

	@SuppressWarnings({ "unchecked", "rawtypes" })
	private static void setEnumField(Object obj, String value, String name)
			throws SecurityException, NoSuchFieldException, IllegalArgumentException, IllegalAccessException {
		Field f = obj.getClass().getField(name);
		f.set(obj, Enum.valueOf((Class<Enum>) f.getType(), value));
	}
	
	//follwoing code for android 5.0+
	
	public static void setStaticIpConfiguration(WifiManager manager,  
            WifiConfiguration config, InetAddress ipAddress, int prefixLength,  
            InetAddress gateway, InetAddress[] dns)  
            throws ClassNotFoundException, IllegalAccessException,  
            IllegalArgumentException, InvocationTargetException,  
            NoSuchMethodException, NoSuchFieldException, InstantiationException {  
        // First set up IpAssignment to STATIC.  
        Object ipAssignment = getEnumValue(  
                "android.net.IpConfiguration$IpAssignment", "STATIC");  
        callMethod(config, "setIpAssignment",  
                new String[] { "android.net.IpConfiguration$IpAssignment" },  
                new Object[] { ipAssignment });  
  
        // Then set properties in StaticIpConfiguration.  
        Object staticIpConfig = newInstance("android.net.StaticIpConfiguration");  
        Object linkAddress = newInstance("android.net.LinkAddress",  
                new Class[] { InetAddress.class, int.class }, new Object[] {  
                        ipAddress, prefixLength });  
  
        setField(staticIpConfig, "ipAddress", linkAddress);  
        setField(staticIpConfig, "gateway", gateway);  
  
       ArrayList<Object> aa= (ArrayList<Object>) getField(staticIpConfig, "dnsServers");  
       aa.clear();  
        for (int i = 0; i < dns.length; i++)  
            aa.add(dns[i]);  
        callMethod(config, "setStaticIpConfiguration",  
                new String[] { "android.net.StaticIpConfiguration" },  
                new Object[] { staticIpConfig });  
        manager.updateNetwork(config);  
        manager.saveConfiguration();  
        //System.out.println("ttttttttttt"+"成功");  
    }  
  
    private static Object newInstance(String className)  
            throws ClassNotFoundException, InstantiationException,  
            IllegalAccessException, NoSuchMethodException,  
            IllegalArgumentException, InvocationTargetException {  
        return newInstance(className, new Class[0], new Object[0]);  
    }  
  
    private static Object newInstance(String className,  
            Class[] parameterClasses, Object[] parameterValues)  
            throws NoSuchMethodException, InstantiationException,  
            IllegalAccessException, IllegalArgumentException,  
            InvocationTargetException, ClassNotFoundException {  
        Class clz = Class.forName(className);  
        Constructor constructor = clz.getConstructor(parameterClasses);  
        return constructor.newInstance(parameterValues);  
    }  
  
    @SuppressWarnings({ "unchecked", "rawtypes" })  
    private static Object getEnumValue(String enumClassName, String enumValue)  
            throws ClassNotFoundException {  
        Class enumClz = (Class) Class.forName(enumClassName);  
        return Enum.valueOf(enumClz, enumValue);  
    }  
  
    private static void setField(Object object, String fieldName, Object value)  
            throws IllegalAccessException, IllegalArgumentException,  
            NoSuchFieldException {  
        Field field = object.getClass().getDeclaredField(fieldName);  
        field.set(object, value);  
    }  

    private static void callMethod(Object object, String methodName,  
            String[] parameterTypes, Object[] parameterValues)  
            throws ClassNotFoundException, IllegalAccessException,  
            IllegalArgumentException, InvocationTargetException,  
            NoSuchMethodException {  
        Class[] parameterClasses = new Class[parameterTypes.length];  
        for (int i = 0; i < parameterTypes.length; i++)  
            parameterClasses[i] = Class.forName(parameterTypes[i]);  
  
        Method method = object.getClass().getDeclaredMethod(methodName,  
                parameterClasses);  
        method.invoke(object, parameterValues);  
    }  

    /*	
	void checkRoleConsistent() {//好像沒用到
		// check role
		if(PreROLE !=  -1) {
			ChecknowRole = -1;
				if (mConnectivityManager != null) {
					mNetworkInfo = mConnectivityManager.getNetworkInfo(ConnectivityManager.TYPE_WIFI);
				}
				if (mNetworkInfo.isConnected() == true && mConnectivityManager != null) {
					if (Isconnect == true) {
						String p2p_Ip = "";
						p2p_Ip = getP2PIpAddress();
						if (p2p_Ip.equals("192.168.49.1") == true) {
							ChecknowRole = RoleFlag.CLIENT.getIndex();
						} else {
							ChecknowRole = RoleFlag.RELAY.getIndex();
						}
					}
				} else {
					if (Isconnect == true) {
						ChecknowRole = RoleFlag.GO.getIndex();
					} else {
						ChecknowRole = RoleFlag.NONE.getIndex();
					}
				}
				if(ChecknowRole == RoleFlag.CLIENT.getIndex())
				manager.requestGroupInfo(channel, new WifiP2pManager.GroupInfoListener() {
					@Override
					public void onGroupInfoAvailable(WifiP2pGroup group) {

						if (group != null) {
							if(!group.getClientList().isEmpty()) {
								ChecknowRole = RoleFlag.GO.getIndex();
							}
						}
					}
				});
				
				if(PreROLE ==RoleFlag.CLIENT.getIndex() &&  ChecknowRole == RoleFlag.GO.getIndex() ) {
					PreROLE=  RoleFlag.NONE.getIndex();
					ROLE = RoleFlag.NONE.getIndex();
					removeGroupCheck= false;
					manager.removeGroup(channel, new WifiP2pManager.ActionListener() {
						@Override
						public void onSuccess() {
							Log.d("Wang", "remove group success");
							removeGroupCheck = true;
						}

						@Override
						public void onFailure(int reason) {
							Log.d("Wang", "initial remove group failure");
							removeGroupCheck = true;
						}
					});
					while(removeGroupCheck== false) {
						
					}
				}else if(PreROLE ==RoleFlag.RELAY.getIndex() && ChecknowRole == RoleFlag.GO.getIndex() ){
					PreROLE=  RoleFlag.NONE.getIndex();
					ROLE = RoleFlag.NONE.getIndex();
					removeGroupCheck= false;
					manager.removeGroup(channel, new WifiP2pManager.ActionListener() {
						@Override
						public void onSuccess() {
							Log.d("Wang", "remove group success");
							removeGroupCheck = true;
						}

						@Override
						public void onFailure(int reason) {
							Log.d("Wang", "initial remove group failure");
							removeGroupCheck = true;
						}
					});
					while(removeGroupCheck== false) {
						
					}
				}
		}else {
			return;
		}
	}
*/	  
    
}